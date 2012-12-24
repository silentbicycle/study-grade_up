#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <assert.h>
#include <string.h>
#include <err.h>
#include <time.h>
#include <sys/time.h>

typedef unsigned int I;
typedef unsigned char C;
typedef void V;
#define DO(n,f) do { for (int i=0, _n=(n); i<_n; i++) { f; } } while (0)

//#define LOG(...) printf(__VA_ARGS__)
#define LOG(...) ;

size_t alloc_sz = 0;

static void *alloc(size_t sz) {
    alloc_sz += sz;
    return malloc(sz);
}

static void reset_alloc(void) { alloc_sz = 0; }

/* ideal grade-up/down algorithm, for a vector of unsigned ints where
 * the max is not too large.
 *
 * lim == upper length limit
 * max == largest value in array (assumes min == 0)
 * in  == input array
 * out == result array
 */
static int grade_updown(int up, I lim, I max, I *in, I *out) {
    I *c = alloc(max*sizeof(I)); /* counts */
    if (c == NULL) return -1;
    bzero(c, max*sizeof(I));

    DO(lim, c[in[i]]++);        /* count instances */

    if (up) {                   /* histogram from head */
        DO(max-1, c[i+1] += c[i]);
    } else {                    /* histogram from tail */
        DO(max-1, c[max-i-2] += c[max-i-1]);
    }

    /* convert histogram => permutation vector */
    for (I i=0; i<lim; i++) {
        I idx = in[lim - i - 1];
        I count = c[idx]--;
        out[-1 + count] = lim - i - 1;
    }
    free(c);
    return 0;
}

int grade_up(I lim, I max, I *in, I *out) { return grade_updown(1, lim, max, in, out); }
int grade_down(I lim, I max, I *in, I *out) { return grade_updown(0, lim, max, in, out); }


/***********************/
/* sparse grade_updown */
/***********************/

/* sparse count vector */
typedef struct {
    I bc;                       /* current block count */
    uint8_t bb;                 /* bits per block */
    I *bbs;                     /* block bases (for histogramming) */
    /* Array of block pointers. Alloc'd on demand. Each has 1<<bb cells. */
    I **bs;
} scv;                          /* sparse count vector */

static scv *scv_new(uint8_t block_bits, I block_count_hint) {
    if (block_bits < 8 || block_bits > 30) return NULL; /* badarg */
    scv *v = NULL;
    I *bbs = NULL, **bs = NULL;
#define C(X) { if (X == NULL) goto cleanup; }
    v = alloc(sizeof(*v)); C(v);
    bbs = alloc(block_count_hint*sizeof(I *)); C(bbs);
    bs = alloc(block_count_hint*sizeof(I **)); C(bs);
#undef C
    bzero(v, sizeof(*v));
    bzero(bbs, block_count_hint*sizeof(I *));
    bzero(bs, block_count_hint*sizeof(I **));
    v->bc = block_count_hint;
    v->bb = block_bits;
    v->bbs = bbs;
    v->bs = bs;
    return v;
cleanup:
    if (bs) free(bs);
    if (bbs) free(bbs);
    if (v) free(v);
    return NULL;
}

static void scv_free(scv *c) {
    DO(c->bc, if (c->bs[i]) free(c->bs[i]));
    free(c->bs);
    free(c->bbs);
    free(c);
}

/* Returns an int because alloc can fail... */
static int scv_inc(scv *c, I idx) {
    I bi = idx >> c->bb;         /* block index */
    I bs = 1<<c->bb;             /* block size */
    I ci = idx & (bs-1);         /* cell index in block */

    if (bi < c->bc) {            /* within existing block range? */
        if (c->bs[bi]) {         /* happy case: block exists */
            c->bs[bi][ci]++;
            return 0;
        } else {                 /* alloc block */
            I sz = bs*sizeof(I);
            I *nb = alloc(sz);
            if (nb == NULL) return -1; /* alloc fail */
            bzero(nb, sz);
            c->bs[bi] = nb;
            nb[ci]++;
            return 0;
        }
    } else {                        /* grow block vector */
        I nbc = 2*c->bc;            /* peacock */
        if (nbc < c->bc) return -1; /* overflow */
        I *nbbs = alloc(nbc*sizeof(I));
        if (nbbs == NULL) return -1; /* alloc fail */
        I **nbs = alloc(nbc*sizeof(I *));
        if (nbs == NULL) { free(nbbs); return -1; }
        /* could use memcpy */
        DO(c->bc, nbbs[i] = c->bbs[i]);
        DO(c->bc, nbs[i] = c->bs[i]);
        free(c->bbs);
        c->bbs = nbbs;
        free(c->bs);
        c->bs = nbs;
        c->bc = nbc;
        return scv_inc(c, idx);
    }
}

static void scv_histo(scv *c, int up) {
    I cur = 0;                   /* running total */
    I bs = 1<<c->bb;             /* block size */
    if (up) {                    /* histo from head */
        for (I bi=0; bi<c->bc; bi++) {
            I *b = c->bs[bi];
            if (b) {             /* if block exists (=> has content) */
                for (I ci=0; ci<bs; ci++) {
                    b[ci] += cur;
                    cur = b[ci];
                }
            } else {             /* just bump base */
                c->bbs[bi] = cur;
            }
        }
    } else {                     /* from tail */
        /* Haven't bothered implementing this since the sparse variant
         * is consistently slower. Ah well. */
        /* TODO */ assert(0);
    }
}

static I scv_fetch_and_decrement(scv *c, I idx) {
    I bi = idx >> c->bb;         /* block index */
    I bs = 1<<c->bb;             /* block size */
    I ci = idx & (bs-1);         /* cell index in block */
    assert(bi < c->bc);

    I *b = c->bs[bi];
    assert(b);
    return b[ci]--;
}

static int sparse_grade_updown(int up, I lim, I *in, I *out) {
    scv *c = scv_new(10, 1);
    if (c == NULL) return -1;

    for (I i=0; i<lim; i++) {
        if (scv_inc(c, in[i]) < 0) {
            scv_free(c);
            /* ALLOC FAIL */
            return -1;
        }
    }
    scv_histo(c, up);

    /* convert histogram => permutation vector */
    for (I i=0; i<lim; i++) {
        I idx = in[lim - i - 1];
        I count = scv_fetch_and_decrement(c, idx);
        out[-1 + count] = lim - i - 1;
    }

    scv_free(c);
    return 0;
}

int sparse_grade_up(I lim, I *in, I *out) { return sparse_grade_updown(1, lim, in, out); }
int sparse_grade_down(I lim, I *in, I *out) { return sparse_grade_updown(0, lim, in, out); }


/************************
 * uint8_t grade_updown *
 ************************/

/* Same as (int) grade_updown, except max is assumed to be 256 since a char is 1 byte. */
static int char_grade_updown(int up, I lim, C *in, I *out) {
    I c[256];                   /* counts */
    bzero(c, 256*sizeof(I));

    DO(lim, c[in[i]]++);        /* count instances */

    if (up) {                   /* histogram from head */
        DO(255, c[i+1] += c[i]);
    } else                      /* histogram from tail */ {
        DO(255, c[256-i-2] += c[256-i-1]);
    }

    /* convert histogram => permutation vector */
    for (I i=0; i<lim; i++) {
        I idx = in[lim - i - 1];
        I count = c[idx]--;
        out[-1 + count] = lim - i - 1;
    }
    return 0;
}

int char_grade_up(I lim, C *in, I *out) { return char_grade_updown(1, lim, in, out); }
int char_grade_down(I lim, C *in, I *out) { return char_grade_updown(0, lim, in, out); }


/**********************
 * merge grade_updown *
 **********************/

typedef struct {
    I len;
    V *v;
} A;                            /* array */

/* Comparison callback, should return:
 *     a[ia] <= a[ib] if up, or
 *     a[ia] >= a[ib] if !up. */
typedef int cmp_fun(A *a, int up, I ia, I ib);

static void merger(int up, A *a, cmp_fun *cmp, I *out, I *tmp, I low, I mid, I high) {
    I i, j, k;
    /* copy current range into tmp buffer */
    for (i=low; i<=high; i++) tmp[i]=out[i];
    i = low; j = mid + 1; k = low;

    /* merge [low,mid] and [mid+1,high] into output */
    while (i <= mid && j <= high) {
        if (cmp(a, up, tmp[i], tmp[j])) {
            out[k++] = tmp[i++];
        } else {
            out[k++] = tmp[j++];
        }
    }

    /* merge remaining, if any */
    while (i <= mid) out[k++] = tmp[i++];
}

/* Special-case the pairwise comparison? It's worth special casing because it's
 * called a _LOT_, but as-is it only makes a small difference +/- timewise. */
#define MERGE_PAIR_AT_BOTTOM 0

#if MERGE_PAIR_AT_BOTTOM
static void merge_pair(int up, A *a, cmp_fun *cmp, I *out, I *tmp, I low, I high) {
    /* Check if they need to be swapped. */
    if (!cmp(a, up, out[low], out[high])) {
        I x = out[low];
        out[low] = out[high];
        out[high] = x;
    }
}
#endif

static void do_merge_grade(int up, A *a, cmp_fun *cmp, I *out, I *tmp, I low, I high) {
    /* should do another sort with small high - low */
    I diff = high - low;
    if (diff == 0) {
        return;
#if MERGE_PAIR_AT_BOTTOM
    } else if (diff == 1) {
        /* Bottom out the recursion and just do it linearly.
         * Will need to be type-specific. */
        merge_pair(up, a, cmp, out, tmp, low, high);
#endif
    } else {
        I mid = low + (high - low) / 2;
        /* these two could be done in parallel */
        do_merge_grade(up, a, cmp, out, tmp, low, mid);
        do_merge_grade(up, a, cmp, out, tmp, mid + 1, high);
        merger(up, a, cmp, out, tmp, low, mid, high);
    }
}

static int merge_grade(int up, I len, cmp_fun *cmp, V *in, I *out) {
    I *tmp = alloc(len * sizeof(I));
    if (tmp == NULL) return -1;
    bzero(tmp, sizeof(tmp));
    A a;
    a.len = len;
    a.v = in;
    DO(len,out[i]=i);           /* out:!len */

    do_merge_grade(up,&a,cmp,out,tmp,0,len-1);
    return 0;
}

int merge_grade_up(I len, cmp_fun *cmp, V *in, I *out) { return merge_grade(1, len, cmp, in, out); }
int merge_grade_down(I len, cmp_fun *cmp, V *in, I *out) { return merge_grade(0, len, cmp, in, out); }


/********
 * main *
 ********/

/* Integer vector comparison callback */
static int ivec_cmp(A *a, int up, I ia, I ib) {
    I *d = (I *)a->v;
    if (up) {
        return d[ia] <= d[ib];
    } else {
        return d[ia] >= d[ib];
    }
}

#define TIME(NAME)                                                      \
    struct timeval NAME ## _tv;                                         \
    gettimeofday(&NAME ## _tv, NULL);                                   \
    clock_t NAME = clock()

#define DELTA(N) \
        long dc_ ## N = N ## _post - N ## _pre;                         \
        double dw_ ## N = N ## _post_tv.tv_sec - N ## _pre_tv.tv_sec    \
          + 1.0e-6 * (N ## _post_tv.tv_usec - N ## _pre_tv.tv_usec);    \
        printf("%-5s %7.3f clock    %8.3f wall time    %.3f million cells/sec.   %lu bytes alloc'd\n", \
            #N,                                                         \
            dc_ ## N / (1.0*CLOCKS_PER_SEC),                            \
            dw_ ## N,                                                   \
            (lim / 1e6) / dw_ ## N, alloc_sz);                          \
        reset_alloc()

#define CHECK_UP()                                                      \
    for (int i=0; i<lim; i++) {                                         \
        LOG("%d: %5d -> %5d (%d)\n", i, ivec[i], gv[i], ivec[gv[i]]);   \
        if (i > 0) {                                                    \
            assert(gv[i-1] != gv[i]);                                   \
            assert(ivec[gv[i-1]] <= ivec[gv[i]]);                       \
        }                                                               \
    }

#define CHECK_DOWN()                                                    \
    for (int i=0; i<lim; i++) {                                         \
        LOG("%d: %5d -> %5d (%d)\n", i, ivec[i], gv[i], ivec[gv[i]]);   \
        if (i > 0) {                                                    \
            assert(gv[i-1] != gv[i]);                                   \
            assert(ivec[gv[i-1]] >= ivec[gv[i]]);                       \
        }                                                               \
    }

int main(int argc, char **argv) {
    I lim = (argc > 1 ? atoi(argv[1]) : 1000);
    I seed = (argc > 2 ? atoi(argv[2]) : 23);
    I max = (argc > 3 ? atoi(argv[3]) : 1000);
    srandom(seed);
    I sz = lim * sizeof(I);

    I *ivec = alloc(sz);
    assert(ivec);
    DO(lim, ivec[i] = random() % max);
    
    I *gv = alloc(sz);
    assert(gv);
    reset_alloc();               /* don't count the allocations above */

    #define FAIL() errx(1, "oops\n")

    bzero(gv, sz);
    TIME(gup_pre);
    if (grade_up(lim, max, ivec, gv) < 0) FAIL();
    TIME(gup_post);
    DELTA(gup);
    CHECK_UP();

    bzero(gv, sz);
    TIME(gdown_pre);
    if (grade_down(lim, max, ivec, gv) < 0) FAIL();
    TIME(gdown_post);
    DELTA(gdown);
    CHECK_DOWN();

    bzero(gv, sz);
    TIME(sgup_pre);
    if (sparse_grade_up(lim, ivec, gv) < 0) FAIL();
    TIME(sgup_post);
    DELTA(sgup);
    CHECK_UP();

    bzero(gv, sz);
    TIME(mup_pre);
    if (merge_grade_up(lim, &ivec_cmp, ivec, gv) < 0) FAIL();
    TIME(mup_post);
    DELTA(mup);
    CHECK_UP();

    bzero(gv, sz);
    TIME(mdown_pre);
    if (merge_grade_down(lim, &ivec_cmp, ivec, gv) < 0) FAIL();
    TIME(mdown_post);
    DELTA(mdown);
    CHECK_DOWN();

    free(ivec);
    free(gv);
    return 0;
}
