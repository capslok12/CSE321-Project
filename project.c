#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define BLOCK_SIZE 4096
#define INODE_SIZE 128
#define DIRECT_POINTERS 8
#define NAME_LEN 28

#define FS_MAGIC 0x56534653
#define JOURNAL_MAGIC 0x4A524E4C

#define REC_DATA 0xD0DA
#define REC_COMMIT 0xC0DE

#define JOURNAL_BLOCK_IDX 1
#define JOURNAL_BLOCKS 16
#define INODE_BLOCKS 2
#define DATA_BLOCKS 64
#define INODE_BMAP_IDX (JOURNAL_BLOCK_IDX + JOURNAL_BLOCKS)
#define DATA_BMAP_IDX (INODE_BMAP_IDX + 1)
#define INODE_START_IDX (DATA_BMAP_IDX + 1)
#define DATA_START_IDX (INODE_START_IDX + INODE_BLOCKS)
#define TOTAL_BLOCKS (DATA_START_IDX + DATA_BLOCKS)

struct superblock {
    uint32_t magic;
    uint32_t block_size;
    uint32_t total_blocks;
    uint32_t inode_count;
    uint32_t journal_block;
    uint32_t inode_bitmap;
    uint32_t data_bitmap;
    uint32_t inode_start;
    uint32_t data_start;
    uint8_t _pad[128 - 9*4];
};

struct inode {
    uint16_t type;
    uint16_t links;
    uint32_t size;
    uint32_t direct[DIRECT_POINTERS];
    uint32_t ctime;
    uint32_t mtime;
    uint8_t _pad[128 - (2+2+4+8*4+4+4)];
};

struct dirent {
    uint32_t inode;
    char name[NAME_LEN];
};

struct journal_header {
    uint32_t magic;
    uint32_t nbytes_used;
};

struct rec_header {
    uint16_t type;
    uint16_t size;
};

struct data_record {
    struct rec_header hdr;
    uint32_t block_no;
    uint8_t data[BLOCK_SIZE];
};

struct commit_record {
    struct rec_header hdr;
};

/* Helper functions */
static void die(const char *msg) {
    perror(msg);
    exit(1);
}

static void read_block(int fd, uint32_t blk, void *buf) {
    if (lseek(fd, blk * BLOCK_SIZE, SEEK_SET) < 0) die("lseek");
    if (read(fd, buf, BLOCK_SIZE) != BLOCK_SIZE) die("read_block");
}

static void write_block(int fd, uint32_t blk, void *buf) {
    if (lseek(fd, blk * BLOCK_SIZE, SEEK_SET) < 0) die("lseek");
    if (write(fd, buf, BLOCK_SIZE) != BLOCK_SIZE) die("write_block");
}

static int bitmap_find_free(uint8_t *bmap, int max) {
    for (int i = 0; i < max; i++)
        if (!(bmap[i/8] & (1 << (i%8))))
            return i;
    return -1;
}

static void bitmap_set(uint8_t *bmap, int idx) {
    bmap[idx/8] |= (1 << (idx%8));
}

/* Journal Management Functions */
static void init_journal_if_needed(int fd, struct superblock *sb) {
    struct journal_header jh;
    if (lseek(fd, sb->journal_block * BLOCK_SIZE, SEEK_SET) < 0) die("lseek");
    if (read(fd, &jh, sizeof(jh)) != sizeof(jh)) die("read");

    if (jh.magic != JOURNAL_MAGIC) {
        jh.magic = JOURNAL_MAGIC;
        jh.nbytes_used = sizeof(jh);
        if (lseek(fd, sb->journal_block * BLOCK_SIZE, SEEK_SET) < 0) die("lseek");
        if (write(fd, &jh, sizeof(jh)) != sizeof(jh)) die("write");
    }
}

static int append_to_journal(int fd, struct superblock *sb, void *record, size_t size) {
    struct journal_header jh;

    if (lseek(fd, sb->journal_block * BLOCK_SIZE, SEEK_SET) < 0) die("lseek");
    if (read(fd, &jh, sizeof(jh)) != sizeof(jh)) die("read");

    if (jh.nbytes_used + size > JOURNAL_BLOCKS * BLOCK_SIZE) {
        fprintf(stderr, "Journal full. Run 'install' first.\n");
        return -1;
    }

    if (lseek(fd, sb->journal_block * BLOCK_SIZE + jh.nbytes_used, SEEK_SET) < 0) die("lseek");
    if (write(fd, record, size) != (ssize_t)size) die("write");

    jh.nbytes_used += size;
    if (lseek(fd, sb->journal_block * BLOCK_SIZE, SEEK_SET) < 0) die("lseek");
    if (write(fd, &jh, sizeof(jh)) != sizeof(jh)) die("write");

    return 0;
}

static void read_superblock(int fd, struct superblock *sb) {
    if (lseek(fd, 0, SEEK_SET) < 0) die("lseek");
    if (read(fd, sb, sizeof(*sb)) != sizeof(*sb)) die("read");

    if (sb->magic != FS_MAGIC) {
        fprintf(stderr, "Invalid filesystem magic: 0x%08x\n", sb->magic);
        exit(1);
    }
}

/* Create command */
static void cmd_create(int fd, struct superblock *sb, const char *filename) {
    init_journal_if_needed(fd, sb);

    uint8_t inode_bmap[BLOCK_SIZE];
    uint8_t data_bmap[BLOCK_SIZE];
    read_block(fd, sb->inode_bitmap, inode_bmap);
    read_block(fd, sb->data_bitmap, data_bmap);

    int new_ino = bitmap_find_free(inode_bmap, 64);
    if (new_ino < 0) die("no free inode");

    uint8_t new_inode_bmap[BLOCK_SIZE];
    memcpy(new_inode_bmap, inode_bmap, BLOCK_SIZE);
    bitmap_set(new_inode_bmap, new_ino);

    uint8_t inode_block_buf[BLOCK_SIZE];
    read_block(fd, sb->inode_start, inode_block_buf);
    struct inode *root = (struct inode *)inode_block_buf;

    uint8_t dir_block[BLOCK_SIZE];
    read_block(fd, root->direct[0], dir_block);

    struct inode new_inode = {0};
    new_inode.type = 1;
    new_inode.links = 1;
    new_inode.size = 0;
    new_inode.ctime = time(NULL);
    new_inode.mtime = time(NULL);

    uint32_t inode_block_num = sb->inode_start + (new_ino / 32);
    uint32_t inode_offset = (new_ino % 32) * INODE_SIZE;

    uint8_t new_inode_block[BLOCK_SIZE];
    read_block(fd, inode_block_num, new_inode_block);
    memcpy(new_inode_block + inode_offset, &new_inode, sizeof(new_inode));

    uint8_t new_dir_block[BLOCK_SIZE];
    memcpy(new_dir_block, dir_block, BLOCK_SIZE);

    struct dirent *de = (struct dirent *)new_dir_block;
    int entries = root->size / sizeof(struct dirent);

    de[entries].inode = new_ino;
    strncpy(de[entries].name, filename, NAME_LEN - 1);
    de[entries].name[NAME_LEN - 1] = '\0';

    uint8_t new_root_inode_block[BLOCK_SIZE];
    memcpy(new_root_inode_block, inode_block_buf, BLOCK_SIZE);
    struct inode *new_root = (struct inode *)new_root_inode_block;
    new_root->size += sizeof(struct dirent);
    new_root->mtime = time(NULL);

    struct data_record dr1 = {
        .hdr = {.type = REC_DATA, .size = sizeof(struct data_record)},
        .block_no = sb->inode_bitmap
    };
    memcpy(dr1.data, new_inode_bmap, BLOCK_SIZE);
    if (append_to_journal(fd, sb, &dr1, sizeof(dr1)) < 0) return;

    struct data_record dr2 = {
        .hdr = {.type = REC_DATA, .size = sizeof(struct data_record)},
        .block_no = inode_block_num
    };
    memcpy(dr2.data, new_inode_block, BLOCK_SIZE);
    if (append_to_journal(fd, sb, &dr2, sizeof(dr2)) < 0) return;

    struct data_record dr3 = {
        .hdr = {.type = REC_DATA, .size = sizeof(struct data_record)},
        .block_no = root->direct[0]
    };
    memcpy(dr3.data, new_dir_block, BLOCK_SIZE);
    if (append_to_journal(fd, sb, &dr3, sizeof(dr3)) < 0) return;

    struct data_record dr4 = {
        .hdr = {.type = REC_DATA, .size = sizeof(struct data_record)},
        .block_no = sb->inode_start
    };
    memcpy(dr4.data, new_root_inode_block, BLOCK_SIZE);
    if (append_to_journal(fd, sb, &dr4, sizeof(dr4)) < 0) return;

    struct commit_record cr = {
        .hdr = {.type = REC_COMMIT, .size = sizeof(struct commit_record)}
    };
    if (append_to_journal(fd, sb, &cr, sizeof(cr)) < 0) return;

    printf("Created journal entry for file '%s'\n", filename);
}

/* Install command */
static void cmd_install(int fd, struct superblock *sb) {
    struct journal_header jh;

    if (lseek(fd, sb->journal_block * BLOCK_SIZE, SEEK_SET) < 0) die("lseek");
    if (read(fd, &jh, sizeof(jh)) != sizeof(jh)) die("read");

    if (jh.magic != JOURNAL_MAGIC) {
        fprintf(stderr, "Journal not initialized or corrupted\n");
        exit(1);
    }

    if (jh.nbytes_used == sizeof(jh)) {
        printf("Journal is empty\n");
        return;
    }

    uint32_t pos = sizeof(jh);
    int in_transaction = 0;

    while (pos < jh.nbytes_used) {
        struct rec_header rh;
        if (lseek(fd, sb->journal_block * BLOCK_SIZE + pos, SEEK_SET) < 0) die("lseek");
        if (read(fd, &rh, sizeof(rh)) != sizeof(rh)) die("read");

        if (rh.type == REC_DATA) {
            struct data_record dr;
            if (lseek(fd, sb->journal_block * BLOCK_SIZE + pos, SEEK_SET) < 0) die("lseek");
            if (read(fd, &dr, sizeof(dr)) != sizeof(dr)) die("read");

            if (in_transaction) {
                write_block(fd, dr.block_no, dr.data);
            }

            pos += rh.size;
        } else if (rh.type == REC_COMMIT) {
            in_transaction = 1;
            struct commit_record cr;
            if (lseek(fd, sb->journal_block * BLOCK_SIZE + pos, SEEK_SET) < 0) die("lseek");
            if (read(fd, &cr, sizeof(cr)) != sizeof(cr)) die("read");

            pos += rh.size;
            in_transaction = 0;
        } else {
            fprintf(stderr, "Unknown record type: 0x%04x\n", rh.type);
            break;
        }
    }

    jh.nbytes_used = sizeof(jh);
    if (lseek(fd, sb->journal_block * BLOCK_SIZE, SEEK_SET) < 0) die("lseek");
    if (write(fd, &jh, sizeof(jh)) != sizeof(jh)) die("write");

    printf("Applied journaled changes\n");
}

/* Main */
int main(int argc, char *argv[]) {
    if (argc < 3) {
        fprintf(stderr, "Usage: %s <img> <command> [args]\n", argv[0]);
        fprintf(stderr, "Commands:\n");
        fprintf(stderr, "  create <filename>  - Journal a new file creation\n");
        fprintf(stderr, "  install            - Apply journaled changes\n");
        return 1;
    }

    int fd = open(argv[1], O_RDWR);
    if (fd < 0) die("open");

    struct superblock sb;
    read_superblock(fd, &sb);

    if (strcmp(argv[2], "create") == 0) {
        if (argc < 4) {
            fprintf(stderr, "Usage: %s <img> create <filename>\n", argv[0]);
            close(fd);
            return 1;
        }
        cmd_create(fd, &sb, argv[3]);
    } else if (strcmp(argv[2], "install") == 0) {
        cmd_install(fd, &sb);
    } else {
        fprintf(stderr, "Unknown command: %s\n", argv[2]);
        close(fd);
        return 1;
    }

    close(fd);
    return 0;
}
