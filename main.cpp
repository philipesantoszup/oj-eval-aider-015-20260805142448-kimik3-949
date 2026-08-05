// Problem 015 - File Storage (ACMOJ 2545)
//
// Disk-backed sorted block-linked list:
//   * data.bin stores fixed-size blocks of (index, value) entries kept in
//     globally ascending order and chained with `next` pointers.
//   * A sparse in-memory directory maps each block's first key to its block
//     number (only block boundaries are kept in RAM, never the whole data set).
//   * Blocks split on overflow and merge/rebalance on underflow, so every
//     block (except possibly one) is at least half full.
//   * State is persisted across runs via dir.bin + data.bin.

#include <cstdio>
#include <cstdint>
#include <cstring>
#include <utility>
#include <vector>
#include <list>
#include <unordered_map>

namespace {

constexpr int     BLOCK_ENTRIES = 128;            // entries per disk block
constexpr int     MIN_ENTRIES   = BLOCK_ENTRIES / 2;
constexpr int     IDX_LEN       = 65;             // 64-byte index + NUL pad
constexpr int     CACHE_CAP     = 32;             // cached blocks (~0.3 MB)
constexpr int32_t DIR_MAGIC     = 0x46313535;

struct Key {
    char    idx[IDX_LEN];       // NUL padded so memcmp == lexicographic order
    int32_t val;
};

struct Block {
    int32_t n;                  // number of valid entries
    int32_t next;               // next block number in sorted order, -1 = tail
    Key     keys[BLOCK_ENTRIES];
};

struct DirEntry {
    Key     first;              // smallest key stored in this block
    int32_t blockNo;
};

// ---------------------------------------------------------------- state ---
FILE*                g_data = nullptr;
std::vector<DirEntry> g_dir;    // sorted by `first`
std::vector<int32_t>  g_free;   // reusable (freed) block numbers
int32_t               g_hw = 0; // high-water mark: next never-used block number

// ------------------------------------------------------------ key utils ---
inline int keyCmp(const Key& a, const Key& b) {
    int c = std::memcmp(a.idx, b.idx, IDX_LEN);
    if (c != 0) return c;
    if (a.val < b.val) return -1;
    if (a.val > b.val) return 1;
    return 0;
}

inline void makeKey(Key& k, const char* s, int32_t v) {
    std::memset(k.idx, 0, IDX_LEN);
    std::memcpy(k.idx, s, std::strlen(s));  // s <= 64 bytes, rest stays NUL
    k.val = v;
}

// --------------------------------------------------------- raw disk I/O ---
void diskRead(int32_t no, Block& b) {
    std::fseek(g_data, (long)no * (long)sizeof(Block), SEEK_SET);
    std::fread(&b, sizeof(Block), 1, g_data);
}

void diskWrite(int32_t no, const Block& b) {
    std::fseek(g_data, (long)no * (long)sizeof(Block), SEEK_SET);
    std::fwrite(&b, sizeof(Block), 1, g_data);
}

// ------------------------------------------- write-through block cache ----
struct Slot {
    int32_t no;
    Block   b;
};
std::list<Slot>                                      g_lru;  // front = MRU
std::unordered_map<int32_t, std::list<Slot>::iterator> g_pos;

void cacheEvictIfFull() {
    while ((int)g_lru.size() >= CACHE_CAP) {
        g_pos.erase(g_lru.back().no);
        g_lru.pop_back();
    }
}

void readBlock(int32_t no, Block& out) {
    auto it = g_pos.find(no);
    if (it != g_pos.end()) {
        g_lru.splice(g_lru.begin(), g_lru, it->second);
        out = it->second->b;
        return;
    }
    cacheEvictIfFull();
    Slot s;
    s.no = no;
    diskRead(no, s.b);
    g_lru.push_front(std::move(s));
    g_pos[no] = g_lru.begin();
    out = g_lru.front().b;
}

void writeBlock(int32_t no, const Block& b) {
    auto it = g_pos.find(no);
    if (it != g_pos.end()) {
        g_lru.splice(g_lru.begin(), g_lru, it->second);
        it->second->b = b;
    } else {
        cacheEvictIfFull();
        Slot s;
        s.no = no;
        s.b  = b;
        g_lru.push_front(std::move(s));
        g_pos[no] = g_lru.begin();
    }
    diskWrite(no, b);
}

void dropBlock(int32_t no) {
    auto it = g_pos.find(no);
    if (it != g_pos.end()) {
        g_lru.erase(it->second);
        g_pos.erase(it);
    }
}

// ------------------------------------------------------- block management -
int32_t allocBlock() {
    if (!g_free.empty()) {
        int32_t x = g_free.back();
        g_free.pop_back();
        return x;
    }
    return g_hw++;
}

void freeBlock(int32_t no) {
    dropBlock(no);
    g_free.push_back(no);
}

// Index of the block that may contain key k (g_dir must be non-empty):
// the last block whose first key is <= k, clamped to block 0.
int findBlockIdx(const Key& k) {
    int lo = 0, hi = (int)g_dir.size();
    while (lo < hi) {
        int mid = (lo + hi) >> 1;
        if (keyCmp(g_dir[mid].first, k) <= 0) lo = mid + 1;
        else hi = mid;
    }
    return lo == 0 ? 0 : lo - 1;
}

// ------------------------------------------------------------- operations -
void rebalance(int di);

void insertEntry(const Key& k) {
    if (g_dir.empty()) {
        int32_t no = allocBlock();
        Block b;
        b.n = 1;
        b.next = -1;
        b.keys[0] = k;
        writeBlock(no, b);
        DirEntry de;
        de.first = k;
        de.blockNo = no;
        g_dir.push_back(de);
        return;
    }
    int di = findBlockIdx(k);
    int32_t no = g_dir[di].blockNo;
    Block b;
    readBlock(no, b);
    int pos = 0;
    while (pos < b.n && keyCmp(b.keys[pos], k) < 0) ++pos;
    // Input guarantees no exact (index, value) duplicate is ever inserted.
    if (b.n < BLOCK_ENTRIES) {
        std::memmove(b.keys + pos + 1, b.keys + pos, (b.n - pos) * sizeof(Key));
        b.keys[pos] = k;
        ++b.n;
        if (pos == 0) g_dir[di].first = k;
        writeBlock(no, b);
        return;
    }
    // Split the full block with the new key included.
    Key tmp[BLOCK_ENTRIES + 1];
    std::memcpy(tmp, b.keys, pos * sizeof(Key));
    tmp[pos] = k;
    std::memcpy(tmp + pos + 1, b.keys + pos, (b.n - pos) * sizeof(Key));
    const int total  = BLOCK_ENTRIES + 1;
    const int leftN  = total / 2;
    const int rightN = total - leftN;
    int32_t rno = allocBlock();
    Block rb;
    rb.n    = rightN;
    rb.next = b.next;
    std::memcpy(rb.keys, tmp + leftN, rightN * sizeof(Key));
    b.n    = leftN;
    b.next = rno;
    std::memcpy(b.keys, tmp, leftN * sizeof(Key));
    writeBlock(no, b);
    writeBlock(rno, rb);
    g_dir[di].first = b.keys[0];
    DirEntry de;
    de.first   = rb.keys[0];
    de.blockNo = rno;
    g_dir.insert(g_dir.begin() + di + 1, de);
}

void deleteEntry(const Key& k) {
    if (g_dir.empty()) return;
    int di = findBlockIdx(k);
    int32_t no = g_dir[di].blockNo;
    Block b;
    readBlock(no, b);
    int pos = 0;
    while (pos < b.n && keyCmp(b.keys[pos], k) < 0) ++pos;
    if (pos >= b.n || keyCmp(b.keys[pos], k) != 0) return;  // may not exist
    std::memmove(b.keys + pos, b.keys + pos + 1, (b.n - pos - 1) * sizeof(Key));
    --b.n;
    if (b.n == 0) {
        if (di > 0) {
            Block pb;
            readBlock(g_dir[di - 1].blockNo, pb);
            pb.next = b.next;
            writeBlock(g_dir[di - 1].blockNo, pb);
        }
        freeBlock(no);
        g_dir.erase(g_dir.begin() + di);
        return;
    }
    if (pos == 0) g_dir[di].first = b.keys[0];
    writeBlock(no, b);
    if (g_dir.size() > 1 && b.n < MIN_ENTRIES) rebalance(di);
}

void rebalance(int di) {
    Block b;
    readBlock(g_dir[di].blockNo, b);
    if (b.n >= MIN_ENTRIES) return;
    if (di + 1 < (int)g_dir.size()) {               // try the next block
        Block nb;
        readBlock(g_dir[di + 1].blockNo, nb);
        if (b.n + nb.n <= BLOCK_ENTRIES) {          // merge nb into b
            std::memcpy(b.keys + b.n, nb.keys, nb.n * sizeof(Key));
            b.n   += nb.n;
            b.next = nb.next;
            writeBlock(g_dir[di].blockNo, b);
            freeBlock(g_dir[di + 1].blockNo);
            g_dir.erase(g_dir.begin() + di + 1);
        } else {                                    // steal nb's first key
            b.keys[b.n++] = nb.keys[0];
            std::memmove(nb.keys, nb.keys + 1, (nb.n - 1) * sizeof(Key));
            --nb.n;
            g_dir[di + 1].first = nb.keys[0];
            writeBlock(g_dir[di].blockNo, b);
            writeBlock(g_dir[di + 1].blockNo, nb);
        }
        return;
    }
    if (di > 0) {                                   // use the previous block
        Block pb;
        readBlock(g_dir[di - 1].blockNo, pb);
        if (pb.n + b.n <= BLOCK_ENTRIES) {          // merge b into pb
            std::memcpy(pb.keys + pb.n, b.keys, b.n * sizeof(Key));
            pb.n   += b.n;
            pb.next = b.next;
            writeBlock(g_dir[di - 1].blockNo, pb);
            freeBlock(g_dir[di].blockNo);
            g_dir.erase(g_dir.begin() + di);
        } else {                                    // steal pb's last key
            std::memmove(b.keys + 1, b.keys, b.n * sizeof(Key));
            b.keys[0] = pb.keys[pb.n - 1];
            ++b.n;
            --pb.n;
            g_dir[di].first = b.keys[0];
            writeBlock(g_dir[di - 1].blockNo, pb);
            writeBlock(g_dir[di].blockNo, b);
        }
    }
}

// ---------------------------------------------------------------- output --
struct OutBuf {
    static constexpr size_t CAP = 1 << 16;  // 64 KB: small so RSS stays low
    char   buf[CAP];
    size_t len = 0;

    void flush() {
        if (len) {
            std::fwrite(buf, 1, len, stdout);
            len = 0;
        }
    }
    void ensure(size_t need) { if (len + need > CAP) flush(); }
    void putc(char c) { ensure(1); buf[len++] = c; }
    void write(const char* s) {
        size_t l = std::strlen(s);
        ensure(l);
        std::memcpy(buf + len, s, l);
        len += l;
    }
    void writeInt(int32_t v) {
        ensure(16);
        uint32_t x = (uint32_t)v;
        char tmp[12];
        int t = 0;
        if (x == 0) tmp[t++] = '0';
        while (x) { tmp[t++] = char('0' + x % 10); x /= 10; }
        while (t) buf[len++] = tmp[--t];
    }
};

OutBuf g_out;

void findEntries(const Key& lo) {   // lo = (index, 0): smallest key for index
    if (g_dir.empty()) {
        g_out.write("null\n");
        return;
    }
    int di = findBlockIdx(lo);
    int32_t no = g_dir[di].blockNo;
    bool any = false;
    while (no != -1) {
        Block b;
        readBlock(no, b);
        for (int i = 0; i < b.n; ++i) {
            int c = std::memcmp(b.keys[i].idx, lo.idx, IDX_LEN);
            if (c == 0) {
                if (any) g_out.putc(' ');
                g_out.writeInt(b.keys[i].val);
                any = true;
            } else if (c > 0) {     // passed every entry with this index
                if (!any) g_out.write("null");
                g_out.putc('\n');
                return;
            }
        }
        no = b.next;
    }
    if (!any) g_out.write("null");
    g_out.putc('\n');
}

// ----------------------------------------------------------------- input --
struct InBuf {
    static constexpr size_t CAP = 1 << 16;  // 64 KB: small so RSS stays low
    char   buf[CAP];
    size_t pos = 0, len = 0;

    int get() {
        if (pos == len) {
            len = std::fread(buf, 1, CAP, stdin);
            pos = 0;
            if (len == 0) return -1;
        }
        return (unsigned char)buf[pos++];
    }
    static bool isWs(int c) {
        return c == ' ' || c == '\n' || c == '\r' || c == '\t' ||
               c == '\f' || c == '\v';
    }
    int nextNonWs() {
        int c;
        while ((c = get()) != -1 && isWs(c)) {}
        return c;
    }
    bool readToken(char* out, int cap) {
        int c = nextNonWs();
        if (c == -1) return false;
        int n = 0;
        while (c != -1 && !isWs(c)) {
            if (n < cap - 1) out[n++] = (char)c;
            c = get();
        }
        out[n] = '\0';
        return true;
    }
    long long readInt() {           // input integers are non-negative
        int c = nextNonWs();
        long long v = 0;
        while (c >= '0' && c <= '9') {
            v = v * 10 + (c - '0');
            c = get();
        }
        return v;
    }
};

InBuf g_in;

// -------------------------------------------------------- persistence -----
void loadState() {
    g_data = std::fopen("data.bin", "r+b");
    FILE* df = std::fopen("dir.bin", "r+b");
    if (!g_data || !df) {                       // fresh start
        if (g_data) std::fclose(g_data);
        if (df) std::fclose(df);
        g_data = std::fopen("data.bin", "w+b");
        return;
    }
    int32_t magic = 0, hw = 0, cnt = 0;
    bool ok = std::fread(&magic, sizeof(int32_t), 1, df) == 1 &&
              magic == DIR_MAGIC &&
              std::fread(&hw, sizeof(int32_t), 1, df) == 1 && hw >= 0 &&
              std::fread(&cnt, sizeof(int32_t), 1, df) == 1 &&
              cnt >= 0 && cnt < (1 << 24);
    if (ok && cnt > 0) {
        g_dir.resize(cnt);
        ok = std::fread(g_dir.data(), sizeof(DirEntry), cnt, df) == (size_t)cnt;
    }
    if (!ok) {
        g_dir.clear();
        g_hw = 0;
        g_free.clear();
    } else {
        g_hw = hw;
        std::vector<char> used(g_hw, 0);
        for (const DirEntry& e : g_dir)
            if (e.blockNo >= 0 && e.blockNo < g_hw) used[e.blockNo] = 1;
        for (int32_t i = 0; i < g_hw; ++i)
            if (!used[i]) g_free.push_back(i);
    }
    std::fclose(df);
}

void saveState() {
    if (g_data) std::fflush(g_data);
    FILE* df = std::fopen("dir.bin", "wb");
    if (!df) return;
    int32_t magic = DIR_MAGIC;
    int32_t hw    = g_hw;
    int32_t cnt   = (int32_t)g_dir.size();
    std::fwrite(&magic, sizeof(int32_t), 1, df);
    std::fwrite(&hw, sizeof(int32_t), 1, df);
    std::fwrite(&cnt, sizeof(int32_t), 1, df);
    if (cnt > 0) std::fwrite(g_dir.data(), sizeof(DirEntry), cnt, df);
    std::fclose(df);
}

}  // namespace

int main() {
    loadState();
    long long n = g_in.readInt();
    char cmd[16];
    char idxbuf[128];
    for (long long i = 0; i < n; ++i) {
        if (!g_in.readToken(cmd, sizeof(cmd))) break;
        if (cmd[0] == 'i') {                    // insert
            g_in.readToken(idxbuf, sizeof(idxbuf));
            int32_t v = (int32_t)g_in.readInt();
            Key k;
            makeKey(k, idxbuf, v);
            insertEntry(k);
        } else if (cmd[0] == 'd') {             // delete
            g_in.readToken(idxbuf, sizeof(idxbuf));
            int32_t v = (int32_t)g_in.readInt();
            Key k;
            makeKey(k, idxbuf, v);
            deleteEntry(k);
        } else {                                // find
            g_in.readToken(idxbuf, sizeof(idxbuf));
            Key k;
            makeKey(k, idxbuf, 0);
            findEntries(k);
        }
    }
    g_out.flush();
    saveState();
    if (g_data) std::fclose(g_data);
    return 0;
}
