#define _GNU_SOURCE
#include <sched.h>
#include <stdio.h>
#include <zlib.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <openssl/md4.h>
#include <openssl/sha.h>
#include <time.h>


#define ARRAY_SIZE(x) (sizeof(x)/sizeof(x[0]))
#define MAX_COLL 1024

static void sched_setup(void)
{
	int ret;
	size_t size;
	cpu_set_t *set;
	struct sched_param sp;

	set = CPU_ALLOC(2);
	size = CPU_ALLOC_SIZE(2);
	CPU_ZERO_S(size, set);
	CPU_SET_S(0, 2, set);


	memset(&sp, 0, sizeof(sp));
	sp.sched_priority = 99;
	ret = sched_setscheduler(0, SCHED_RR, &sp);
	if (ret < 0) {
		perror("sched_setscheduler");
		exit(-1);
	}
	ret = sched_setaffinity(0, size, set);
	if (ret < 0) {
		perror("sched_setaffinity");
		exit(-1);
	}

	CPU_FREE(set);
}

typedef unsigned long (*tencode)(unsigned char *buf, size_t size);

struct method {
	tencode encode;
	unsigned long long avg_process_time;
	unsigned int samples;
	unsigned int *bucket;
	unsigned int nb_buckets;
	unsigned int total_collisions;
	char *name;
};

static struct method *method_init(char *name, size_t nb_buckets, tencode encode)
{
	struct method *m;
	m = calloc(1, sizeof(*m));
	if (!m)
		return NULL;

	m->bucket = calloc(sizeof(unsigned int), nb_buckets);
	if (!m->bucket) {
		free(m);
		return NULL;
	}

	m->nb_buckets = nb_buckets;
	m->name = strdup(name);
	m->encode = encode;

	return m;
}

struct timespec ts_diff(struct timespec start, struct timespec end)
{
	struct timespec temp;
	if ((end.tv_nsec-start.tv_nsec)<0) {
		temp.tv_sec = end.tv_sec-start.tv_sec-1;
		temp.tv_nsec = 1000000000+end.tv_nsec-start.tv_nsec;
	} else {
		temp.tv_sec = end.tv_sec-start.tv_sec;
		temp.tv_nsec = end.tv_nsec-start.tv_nsec;
	}
	return temp;
}

unsigned long long ts_2_ns(struct timespec *ts)
{
	return (ts->tv_sec * 1000000000) + ts->tv_nsec;
}

static void method_hash(struct method *m, unsigned char *buf, size_t size)
{
	unsigned long hash, bucket;

	hash = m->encode(buf, size);

	m->samples++;

	bucket = hash % m->nb_buckets;
	if (m->bucket[bucket]) {
		m->total_collisions++;
	}

	m->bucket[bucket]++;
}

static void method_free(struct method *m)
{
	free(m->name);
	free(m->bucket);
	free(m);
}

static void method_dump_stats(struct method *m)
{
	int *collisions;
	int i;
	int max_coll = 0;

	collisions = calloc(sizeof(int), MAX_COLL);

	for (i = 0; i < m->nb_buckets; i++) {
		int coll;
		coll = m->bucket[i];

		if (coll < 0 || coll >= MAX_COLL) {
			printf("Weird %s bucket #%d, val %d\n", m->name, i, coll);
			continue;
		}
		collisions[coll]++;
		if (coll > max_coll)
			max_coll = coll;
	}
	printf("%s, %d buckets, %d samples: \n%-8s", m->name, m->nb_buckets, m->samples, "#coll");
	i = 0;
	while (i <= max_coll) {
		printf("%5d ", i);
		i++;
	}
	printf("\n%-8s", "#occur");
	i = 0;
	while (i <= max_coll) {
		printf("%5d ", collisions[i]);
		i++;
	}
	puts("");

	printf("avg. time: %lld ns, ", m->avg_process_time);
	printf("total collisions: %d\n", m->total_collisions);
	puts("");
	free(collisions);
}

static unsigned long rand_encode(unsigned char *buf, size_t size)
{
	return random();
}

static unsigned long sha1_encode(unsigned char *buf, size_t size)
{
	uint8_t sha1[SHA_DIGEST_LENGTH];
	unsigned long *p = (void *)sha1;
	SHA1((unsigned char *)buf, size, sha1);
	return *p;
}

static unsigned long md4_encode(unsigned char *buf, size_t size)
{
	uint8_t md4[MD4_DIGEST_LENGTH];
	unsigned long *p = (void *)md4;
	MD4((unsigned char *)buf, size, md4);
	return *p;
}

static unsigned long crc_encode(unsigned char *buf, size_t size)
{
	unsigned long crc;
	crc = crc32(0, (unsigned char *)buf, size);
	return crc;
}

static unsigned long crc_high_encode(unsigned char *buf, size_t size)
{
	return crc_encode(buf, size) >> (sizeof(unsigned long) / 2);
}

static unsigned long khash_encode(unsigned char *s, size_t size)
{
	unsigned long h = *s;
	if (!h)
		return 0;

	s++;
	while (*s) {
		h = (h << 5) - h + *s;
		s++;
	}
	return h;
}

/* 2^31 + 2^29 - 2^25 + 2^22 - 2^19 - 2^16 + 1 */
#define GOLDEN_RATIO_PRIME_32 0x9e370001UL

static inline uint32_t hash_long(uint32_t val, unsigned int bits)
{
	/* On some cpus multiply is faster, on others gcc will do shifts */
	uint32_t hash = val * GOLDEN_RATIO_PRIME_32;

	/* High bits are more random, so use them. */
	return hash >> (32 - bits);
}


#define BITS_PER_LONG (sizeof(long) * 8)
 __attribute__((unused)) static unsigned long linux_kernel_encode(unsigned char *buf, size_t size)
{
	unsigned long hash = 0;
	unsigned long l = 0;
	int len = 0;
	unsigned char c;

	do {
		if (!(c = *buf++)) {
			c = (char)len;
			len = -1;
		}
		l = (l << 8) | c;
		len++;
		if ((len & (BITS_PER_LONG/8-1))==0)
			hash = hash_long(hash^l, BITS_PER_LONG);
	} while (len);

	return hash;

}

 __attribute__((unused)) static unsigned long libc_encode(unsigned char *buf, size_t size)
{
	unsigned long hval;
	unsigned int count;
	unsigned int len = size;

	/* Compute an value for the given string. Perhaps use a better method. */
	hval = len;
	count = len;
	while (count-- > 0)
	{
		hval <<= 4;
		hval += buf[count];
	}
	return hval;
}

static unsigned long murmur_encode(unsigned char * key, size_t len)
{
	// 'm' and 'r' are mixing constants generated offline.
	// They're not really 'magic', they just happen to work well.
	unsigned int seed = 0xfa;
	const unsigned int m = 0x5bd1e995;
	const int r = 24;

	// Initialize the hash to a 'random' value

	unsigned int h = seed ^ len;

	// Mix 4 bytes at a time into the hash

	const unsigned char * data = (const unsigned char *)key;

	while(len >= 4)
	{
		unsigned int k = *(unsigned int *)data;

		k *= m;
		k ^= k >> r;
		k *= m;

		h *= m;
		h ^= k;

		data += 4;
		len -= 4;
	}

	// Handle the last few bytes of the input array

	switch(len)
	{
		case 3: h ^= data[2] << 16;
		case 2: h ^= data[1] << 8;
		case 1: h ^= data[0];
			h *= m;
	};

	// Do a few final mixes of the hash to ensure the last few
	// bytes are well-incorporated.

	h ^= h >> 13;
	h *= m;
	h ^= h >> 15;

	return h;
}

#define FNV_32_PRIME (0x01000193UL)
static unsigned long fnv1_encode(unsigned char *buf, size_t len)
{
	unsigned long hval = FNV_32_PRIME;
	unsigned char *bp = (unsigned char *)buf;	/* start of buffer */
	unsigned char *be = bp + len;		/* beyond end of buffer */

	/*
	 * FNV-1 hash each octet in the buffer
	 */
	while (bp < be) {

		/* multiply by the 32 bit FNV magic prime mod 2^32 */
#if defined(NO_FNV_GCC_OPTIMIZATION)
		hval *= FNV_32_PRIME;
#else
		hval += (hval<<1) + (hval<<4) + (hval<<7) + (hval<<8) + (hval<<24);
#endif

		/* xor the bottom with the current octet */
		hval ^= (unsigned long)*bp++;
	}

	/* return our new hash value */
	return hval;
}


static unsigned long jenkins_encode(unsigned char *key, size_t key_len)
{
    uint32_t hash = 0;
    size_t i;

    for (i = 0; i < key_len; i++) {
        hash += key[i];
        hash += (hash << 10);
        hash ^= (hash >> 6);
    }
    hash += (hash << 3);
    hash ^= (hash >> 11);
    hash += (hash << 15);
    return hash;
}
#undef get16bits
#if (defined(__GNUC__) && defined(__i386__)) || defined(__WATCOMC__) \
  || defined(_MSC_VER) || defined (__BORLANDC__) || defined (__TURBOC__)
#define get16bits(d) (*((const uint16_t *) (d)))
#endif

#if !defined (get16bits)
#define get16bits(d) ((((uint32_t)(((const uint8_t *)(d))[1])) << 8)\
                       +(uint32_t)(((const uint8_t *)(d))[0]) )
#endif

static unsigned long super_fast_hash_encode(unsigned char * data, size_t len)
{
	uint32_t hash = len, tmp;
	int rem;

	if (len <= 0 || data == NULL)
		return 0;

	rem = len & 3;
	len >>= 2;

	/* Main loop */
	for (;len > 0; len--) {
		hash  += get16bits (data);
		tmp    = (get16bits (data+2) << 11) ^ hash;
		hash   = (hash << 16) ^ tmp;
		data  += 2*sizeof (uint16_t);
		hash  += hash >> 11;
	}

	/* Handle end cases */
	switch (rem) {
		case 3: hash += get16bits (data);
			hash ^= hash << 16;
			hash ^= data[sizeof (uint16_t)] << 18;
			hash += hash >> 11;
			break;
		case 2: hash += get16bits (data);
			hash ^= hash << 11;
			hash += hash >> 17;
			break;
		case 1: hash += *data;
			hash ^= hash << 10;
			hash += hash >> 1;
	}

	/* Force "avalanching" of final 127 bits */
	hash ^= hash << 3;
	hash += hash >> 5;
	hash ^= hash << 4;
	hash += hash >> 17;
	hash ^= hash << 25;
	hash += hash >> 6;

	return hash;
}

/*
  Bacula project hash.c file:
  http://www.koders.com/c/fidBD2D6E36FB86821D1E65D1AFBB0E557896B14C7E.aspx?s=worker_main
 */
static unsigned long bacula_hash(unsigned char * data, size_t len)
{
	int i=0;
	int hashvalue;
	size_t n = len;

	for (n=0; n<len; n++) {
		i=(i<<3)+(*data++ - '0');
	}

	hashvalue = (i*1103515249);

	return hashvalue >> (sizeof(unsigned long) / 4);
}

/*
 * SuperFastHash by Paul Hseih:
 *   http://www.azillionmonkeys.com/qed/hash.html
 *
 * Licensed under BSD according to the following clause from:
 *   http://www.azillionmonkeys.com/qed/weblicense.html
 * "If your code is compatible with the old style BSD license and you wish
 *  to avoid the burden of explicitely protecting code you obtained from
 *  here from misrepresentation then you can simply cover it with
 *  the old-style BSD license."
 */


#undef get16bits
#if (defined(__GNUC__) && defined(__i386__)) || defined(__WATCOMC__) \
  || defined(_MSC_VER) || defined (__BORLANDC__) || defined (__TURBOC__)
#define get16bits(d) (*((const uint16_t *) (d)))
#endif

#if !defined (get16bits)
#define get16bits(d) ((((uint32_t)(((const uint8_t *)(d))[1])) << 8)\
                       +(uint32_t)(((const uint8_t *)(d))[0]) )
#endif

uint32_t SuperFastHash (const char * data, int len) {
    uint32_t hash = len, tmp;
    int rem;

    if (len <= 0 || data == NULL) return 0;

    rem = len & 3;
    len >>= 2;

    /* Main loop */
    for (;len > 0; len--) {
        hash  += get16bits (data);
        tmp    = (get16bits (data+2) << 11) ^ hash;
        hash   = (hash << 16) ^ tmp;
        data  += 2*sizeof (uint16_t);
        hash  += hash >> 11;
    }

    /* Handle end cases */
    switch (rem) {
        case 3: hash += get16bits (data);
                hash ^= hash << 16;
                hash ^= data[sizeof (uint16_t)] << 18;
                hash += hash >> 11;
                break;
        case 2: hash += get16bits (data);
                hash ^= hash << 11;
                hash += hash >> 17;
                break;
        case 1: hash += *data;
                hash ^= hash << 10;
                hash += hash >> 1;
    }

    /* Force "avalanching" of final 127 bits */
    hash ^= hash << 3;
    hash += hash >> 5;
    hash ^= hash << 4;
    hash += hash >> 17;
    hash ^= hash << 25;
    hash += hash >> 6;

    return hash;
}



#define FOREACH(ele, array) do { \
	int n; \
	typeof(array[0]) ele; \
	for (n = 0; ele = array[n], ele != NULL; n++)

#define ENDFOREACH() } while (0);
#define MAX_METHODS 100

int main(int argc, char **argv)
{
	FILE *f;
	char buf[BUFSIZ];
	int cur_size;
	int sizes[] = { 7919, 104729 };
	struct method *m[MAX_METHODS] = { NULL, };

	sched_setup();

	if (2 > argc) {
		puts("Provide the file to read values to hash from");
		exit(0);
	}

	for (cur_size = 0; cur_size < ARRAY_SIZE(sizes); cur_size++) {
		struct timespec after, before, diff;

		m[0] = method_init("crc", sizes[cur_size], crc_encode);
		m[1] = method_init("md4", sizes[cur_size], md4_encode);
		m[2] = method_init("sha1", sizes[cur_size], sha1_encode);
		m[3] = method_init("rand", sizes[cur_size], rand_encode);
		m[4] = method_init("crc_high", sizes[cur_size], crc_high_encode);
		m[5] = method_init("khash", sizes[cur_size], khash_encode);
		m[6] = method_init("murmur", sizes[cur_size], murmur_encode);
		m[7] = method_init("fnv1", sizes[cur_size], fnv1_encode);
		m[8] = method_init("jenkins", sizes[cur_size], jenkins_encode);
		m[9] = method_init("sfh", sizes[cur_size], super_fast_hash_encode);
		m[10] = method_init("bacula hash", sizes[cur_size], bacula_hash);
		m[12] = method_init("libc", sizes[cur_size], libc_encode);
		m[13] = method_init("superfasthash", sizes[cur_size], libc_encode);

		f = fopen(argv[1], "r");
		if (!f) {
			perror("fopen");
			exit(-1);
		}

		/* Preload file */
		while(fgets(buf, sizeof(buf), f)) { }
		rewind(f);

		FOREACH(meth, m) {
			clock_gettime(CLOCK_MONOTONIC, &before);
			while(fgets(buf, sizeof(buf), f)) {
				method_hash(meth, (unsigned char *)buf, strlen(buf));
			}
			clock_gettime(CLOCK_MONOTONIC, &after);
			diff = ts_diff(before, after);
			meth->avg_process_time = ts_2_ns(&diff) / meth->samples;
			rewind(f);
		} ENDFOREACH();


		FOREACH(meth, m) {
			method_dump_stats(meth);
		} ENDFOREACH();

		FOREACH(meth, m) {
			method_free(meth);
		} ENDFOREACH();

		puts("=========================================");

		fclose(f);
	}

	return 0;
}
