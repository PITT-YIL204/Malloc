#include <sys/mman.h>
#include "bool.h"
#include "malloc.h"

/* macros */
#define K 1024
#define M ((unsigned int)1024 * K)
#define G ((unsigned long int)1024 * M)

#define PAGE_SIZE (__page_size)
#define ARENA_SIZE (2 * M + PAGE_SIZE)
#define DISTRICT_SIZE (G + 2 * M)

#define atom_l_n(var) __atomic_load_n((var), __ATOMIC_RELAXED)
#define atom_l(var) __atomic_load((var), __ATOMIC_RELAXED)
#define atom_ce(tar,exp,des) __atomic_compare_exchange((tar), (exp), (des), false, __ATOMIC_RELAXED, __ATOMIC_RELAXED)
#define atom_ce_n(tar,exp,des) __atomic_compare_exchange_n((tar), (exp), (des), false, __ATOMIC_RELAXED, __ATOMIC_RELAXED)
#define atom_keep_ce(tar,exp,des,func) do {func} while (!atom_ce(tar,exp,des))
#define atom_keep_ce_n(tar,exp,des,func) do {func} while (!atom_ce_n(tar,exp,des))

/* type defines */
enum meta_type {unsaturate, saturate = 21, oversaturate};

struct meta {
	size_t arena_offset;
	struct meta *free;
	size_t block_size;
	size_t data_size;
	char data;
};

struct arena {
	struct arena *next;
	struct meta *free;
	size_t memory_used;
};

/* constants */
static const int __page_size;

/* global variables */
static bool init = 0;
static size_t memory_used = 0;
static size_t break_size = 0;
static size_t mmapped_size = 0;
static intptr_t heap[2] = {0};
static struct arena *base[22] = {0};
static intptr_t idle_arena = 0;
static intptr_t developing_dist[2] = {0};
static intptr_t tail = 0;

/* function claims */
static void *uns_malloc(size_t byte);
static void *sat_malloc(size_t byte);
static void *over_malloc(size_t byte);

static void uns_free(void* ptr, size_t byte);
static void sat_free(void* ptr);
static void over_free(void* ptr, size_t byte);

static void *over_realloc(void* ptr, size_t byte);

static size_t get_block_size(void* ptr);
static void initialize(void);
static struct arena *apply_for_arena(void);
static struct arena *create_arena(void);
static struct meta *create_meta(struct arena *arena, size_t block_size, int index);
static size_t apply_for_meta(struct arena *arena, size_t block_size);
static intptr_t apply_for_mmap(size_t block_size);
static void free_arena(struct arena *arena, int index);
static enum meta_type find_meta_type(size_t byte);
static inline int find_size_base(size_t size);
static inline void* get_ptr(intptr_t addr);
static void data_cpy(void* dst, void* src);
static size_t next_pow_2(size_t v);
static int log_2(size_t v);

/* function defines */
void *malloc(size_t byte) {

	if (!init && !__atomic_exchange_n(&init, true,  __ATOMIC_RELAXED))
		initialize();

	void *ptr = NULL;

	switch(find_meta_type(byte)) {
		case unsaturate:
			ptr = uns_malloc(byte);
			break;
		case saturate:
			ptr = sat_malloc(byte);
			break;
		case oversaturate:
			ptr = over_malloc(byte);
	}

	__atomic_add_fetch(&memory_used, byte, __ATOMIC_RELAXED);

	return ptr;

}

void free(void* ptr) {
	if (ptr == NULL) return;

	size_t byte = malloc_size(ptr);

	switch(find_meta_type(byte)) {
	case unsaturate:
		uns_free(ptr, byte);
		break;
	case saturate:
		sat_free(ptr);
		break;
	case oversaturate:
		over_free(ptr, byte);
	}

	__atomic_sub_fetch(&memory_used, byte, __ATOMIC_RELAXED);

	return;
}

void *calloc(size_t num, size_t size) {
	size_t byte = num * size;
	void  *ptr = malloc(byte);
	void *cpy = ptr;
	size_t c64, c32, c16;
	byte -= (c64 = byte / 8);
	byte -= (c32 = byte / 4);
	byte -= (c16 = byte / 2);
	while (c64--) *(long long int*)(cpy++) = 0;
	while (c32--) *(long int*)(cpy++) = 0;
	while (c16--) *(int*)(cpy++) = 0;
	while (byte--) *(char*)(cpy++) = 0;
	return ptr;
}

void *realloc(void *ptr, size_t byte) {
	void *new_ptr;
	size_t block_size;
	size_t data_size = malloc_size(ptr);
	if ((block_size = get_block_size(ptr)) < byte) {
		if (find_meta_type(data_size) == oversaturate) {
			new_ptr = over_realloc(ptr, byte);
		} else {
			new_ptr = malloc(byte);
			data_cpy(new_ptr, ptr);
			free(ptr);
		}
	} else {
		new_ptr = ptr;
	}
	__atomic_sub_fetch(&memory_used, data_size, __ATOMIC_RELAXED);
	__atomic_add_fetch(&memory_used, byte, __ATOMIC_RELAXED);
	return new_ptr;
}

size_t malloc_size(void* ptr) {
	return *(size_t*)(ptr - sizeof(size_t));
}

size_t malloc_memory(void) {
	return atom_l_n(&memory_used);
}

static void *uns_malloc(size_t byte) {
	struct arena *new_arena = NULL;
	struct meta *new_meta = NULL;

	size_t block_size = next_pow_2(byte);
	int index = log_2(block_size);

	struct arena *iter;

	startover:
	iter = atom_l_n(&base[index]);

	if (iter == NULL) {
		if((new_arena = create_arena()) == NULL) return NULL;
		new_meta = create_meta(new_arena, block_size, index);
		atom_keep_ce_n(&(base[index]), &iter, new_arena, 
			new_arena -> next = atom_l_n(&base[index]););
	} else {

		while (atom_l_n(&(iter -> free)) == NULL && ARENA_SIZE < (atom_l_n(&(iter -> memory_used)) + block_size)) {
			if(iter -> next == NULL) break;
			iter = atom_l_n(&(iter -> next));
		}

		if (ARENA_SIZE < (atom_l_n(&(iter -> memory_used)) + block_size)) {
			goto startover;
		} else {
			new_meta = atom_l_n(&(iter -> free));
			atom_keep_ce_n(&(iter -> free), &new_meta, new_meta -> free, 
				if (atom_l_n(&(iter -> free)) == NULL) {
					new_meta = NULL; break;
				});
			if (new_meta == NULL) {
				if((new_meta = create_meta(new_arena, block_size, index)) == NULL) 
					goto startover;
			}
		}
	}

	new_meta -> data_size = byte;

	return (void*)&(new_meta -> data);
}

static void *sat_malloc(size_t byte) {
	struct arena *new_arena = NULL;
	struct arena *iter;
	struct arena *free;

	startover:
	iter = atom_l_n(&base[saturate]);

	if (iter == NULL) {
		if((new_arena = create_arena()) == NULL) return NULL;
	} else {
		while(atom_l_n(&(iter -> free)) == NULL) {
			if(iter -> next == NULL) break;
			iter = atom_l_n(&(iter -> next));
		}
		if (atom_l_n(&(iter -> free)) == NULL) {
			goto startover;
		}
		new_arena = iter;
		free = (struct arena*)atom_l_n(&(iter -> free));
		if (!atom_ce_n(&free, &new_arena, NULL))
			goto startover;

		iter = atom_l_n(&base[saturate]);
		atom_keep_ce(&(iter -> next), &new_arena, &(new_arena -> next),
			while((free = atom_l_n(&(iter -> next))) != new_arena) {
				__atomic_exchange(&iter, &(iter -> next), &free, __ATOMIC_RELAXED);
				if (atom_l_n(&iter) == new_arena) {
					iter = free;
				}
			});
		__atomic_store(&(new_arena -> next), &base[saturate], __ATOMIC_RELAXED);
	}

	new_arena -> memory_used = byte;

	return ((void*)new_arena + sizeof(struct arena));
}

static void *over_malloc(size_t byte) {
	size_t block_size = (next_pow_2(byte / M) + 2) * M;
	intptr_t addr = apply_for_mmap(block_size);
	if (addr == 0) return NULL;

	intptr_t ret = (intptr_t)mmap((void*)addr, block_size, PROT_NONE, MAP_FIXED|MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
	if (ret == -1) return NULL;

	(ret == heap[1]) ? (*(bool*)ret = 1) : (*(bool*)ret = 0);
	ret += sizeof(bool);
	*(size_t*)ret = block_size;
	ret += sizeof(size_t);
	*(size_t*)ret = byte;

	return (void*)ret + sizeof(size_t);
}

static void uns_free(void* ptr, size_t byte) {
	struct meta *meta = ptr - 4 * sizeof(size_t);
	struct arena *arena = (void*)meta - (meta -> arena_offset);

	struct meta *free;
	atom_keep_ce_n(&(arena -> free), &free, meta,
		free = atom_l_n(&(arena -> free));
		meta -> free = free;);

	size_t block_size = meta -> block_size;
	int index = find_size_base(malloc_size(ptr));
	size_t used = atom_l_n(&(arena -> memory_used));

	if (used + block_size + sizeof(struct meta) > ARENA_SIZE) {
		if (atom_ce_n(&(arena -> memory_used), &used, used - block_size - sizeof(struct meta))) {
			struct arena *next = atom_l_n(&base[index]);
			atom_keep_ce_n(&base[index], &next, arena,
				arena -> next = next;);
		} else {
			__atomic_sub_fetch(&(arena -> memory_used), block_size + sizeof(struct meta), __ATOMIC_RELAXED);
		}
	} else if (used == block_size + sizeof(struct meta) + sizeof(struct arena) && atom_l_n(&base[index]) != NULL){
		if (atom_ce_n(&(arena -> memory_used), &used, ARENA_SIZE)) {
			free_arena(arena, index);
		} else {
			__atomic_sub_fetch(&(arena -> memory_used), block_size + sizeof(struct meta), __ATOMIC_RELAXED);
		}
	} else {
		__atomic_sub_fetch(&(arena -> memory_used), block_size + sizeof(struct meta), __ATOMIC_RELAXED);
	}

	return;
}

static void sat_free(void* ptr) {
	struct arena *arena = ptr - sizeof(struct arena);
	arena -> memory_used = 0;
	arena -> free = (struct meta*)arena;
	arena -> next = NULL;
	struct arena *iter = base[saturate];
	struct arena *next, *tmp;
	struct meta *free;
	int c = 0;
	while(true) {
		if (c > 8) {
			madvise(arena, ARENA_SIZE, MADV_DONTNEED);
			if ((next = atom_l_n(&(iter -> next))) == NULL) break;
			if (!atom_ce(&(iter -> next), &next, &(iter -> next -> next))) break;
			arena = next;
			if ((free = atom_l_n(&(arena -> free))) != (struct meta*)arena) break;
			if (!atom_ce_n(&(arena -> free), &free, NULL)) break;
		} else if (atom_l_n(&(iter -> memory_used)) == 0) {
			if ((next = atom_l_n(&(iter -> next))) != NULL) {
				__atomic_exchange(&iter, &(iter -> next), &tmp, __ATOMIC_RELAXED);
				c++;
				if (iter != next) {
					iter = tmp;
					c--;
				}
			} else {
				if (atom_ce_n(&(iter -> next), &next, arena)) break;
			}

		} else {
			iter = base[saturate];
			c = 0;
		}
	}

	return;
}

static void over_free(void* ptr, size_t byte) {
	intptr_t addr = (intptr_t)ptr - 2 * sizeof(size_t) - sizeof(bool);
	if (*(bool*)atom_l_n(&addr)) {
		intptr_t iter = addr;
		size_t block_size = *(size_t*)(iter + sizeof(bool));
		iter += *(size_t*)(iter + sizeof(bool));
		bool *free;
		bool try;

		resume:
		try = 0;
		while (*(free = (bool*)atom_l_n(&iter))) {
			block_size += *(size_t*)(iter + sizeof(bool));
			iter += *(size_t*)(iter + sizeof(bool));
		}

		heap[1] = iter;
		if (!atom_ce_n(free, &try, true))
			goto resume;

		munmap((void*)addr, block_size);
	}
	return;
}

static void *over_realloc(void* ptr, size_t byte) {
	void *new_ptr;
	if (atom_l_n(&developing_dist[0]) + DISTRICT_SIZE >= heap[1])
		goto redistrict;
	intptr_t addr = (intptr_t)ptr - 2 * sizeof(size_t) - sizeof(bool);
	size_t block_size = *(size_t*)(addr + sizeof(bool));
	intptr_t iter = addr + block_size;
	while (*(bool*)atom_l_n(&iter)) {
		*(size_t*)(addr + sizeof(bool)) += *(size_t*)(iter + sizeof(bool) + sizeof(size_t));
		if (*(size_t*)(addr + sizeof(bool)) >= byte + 3 * sizeof(size_t))
			return ptr;
	}

	redistrict:
	new_ptr = malloc(byte);
	data_cpy(ptr, new_ptr);
	free(ptr);

	return new_ptr;

}

static size_t get_block_size(void* ptr) {
	if(find_size_base(malloc_size(ptr)) == 21) 
		return 2 * M;

	return *(size_t*)(ptr - 2 * sizeof(size_t));
}

static void initialize(void) {
	if (init) return;

	*(int*)(&__page_size) = sysconf(_SC_PAGESIZE);

	developing_dist[0] = (heap[0] = (intptr_t)sbrk(0));
	tail = (developing_dist[1] = (heap[1] = heap[0] + 2 * DISTRICT_SIZE));

#ifdef __LINUX__
	madvise(developing_dist[0], DISTRICT_SIZE, MADV_NOHUGEPAGE);
	madvise(developing_dist[1], DISTRICT_SIZE, MADV_HUGEPAGE);
#endif

	idle_arena = heap[0];
	break_size = 4 * ARENA_SIZE;
	*(intptr_t*)(*(intptr_t*)(*(intptr_t*)(sbrk(ARENA_SIZE)) = (intptr_t)sbrk(ARENA_SIZE)) = (intptr_t)sbrk(ARENA_SIZE)) = (intptr_t)sbrk(ARENA_SIZE);
	
	return;
}

static struct arena *create_arena(void) {
	struct arena *new_arena;

	if (idle_arena == 0) {
		if ((new_arena = apply_for_arena()) == NULL) return NULL;
	} else {
		intptr_t addr = atom_l_n(&idle_arena);
		intptr_t next;
		atom_keep_ce_n(&idle_arena, &addr, next, 
			if (atom_l_n(&idle_arena) == 0) {
				addr = 0; break;
			}
			next = (intptr_t)((struct arena*)get_ptr(addr)) -> next;);
		new_arena = (struct arena*)get_ptr(addr);
		if (new_arena == NULL) {
			if ((new_arena = apply_for_arena()) == NULL) return NULL;
		}
	}

	new_arena -> free = NULL;
	new_arena -> memory_used = sizeof(struct arena);
	new_arena -> next = NULL;

	return new_arena;
}

static struct arena *apply_for_arena(void) {
	intptr_t developing = atom_l_n(&developing_dist[0]);
	intptr_t end = developing + DISTRICT_SIZE;
	size_t brk_size = atom_l_n(&break_size);
	if (brk_size + atom_l_n(&heap[0]) + ARENA_SIZE >= end) {
		if (end >= atom_l_n(&heap[1])) return NULL;
		intptr_t developing = end;
		if (atom_ce_n(&developing_dist[0], &developing, end)) {
#ifdef __LINUX__
			madvise(developing_dist[1], DISTRICT_SIZE, MADV_NOHUGEPAGE);
#endif
		}
	}
	brk_size = atom_l_n(&break_size);
	atom_keep_ce_n(&break_size, &brk_size, brk_size + ARENA_SIZE,);

	intptr_t new_arena = (intptr_t)sbrk(ARENA_SIZE);
	if (new_arena == -1) return NULL;
	return (struct arena*)new_arena;
}

static struct meta *create_meta(struct arena *arena, size_t block_size, int index) {
	size_t offset = apply_for_meta(arena, block_size);
	if (offset == 0) {
		struct arena *next;
		struct arena *iter = atom_l_n(&base[index]);
		atom_keep_ce(&(iter -> next), &arena, &(arena -> next),
			while((next = atom_l_n(&(iter -> next))) != arena) {
				__atomic_exchange(&iter, &(iter -> next), &next, __ATOMIC_RELAXED);
				if (atom_l_n(&iter) == arena)
					iter = next;
				if (atom_l_n(&(iter -> memory_used)) == ARENA_SIZE)
					iter = atom_l_n(&base[index]);
				if (atom_l_n(&(iter -> next)) == NULL)
					return NULL;
			});
		atom_ce_n(&(arena -> next), &next, base[index]);
		return NULL;
	}

	struct meta *meta = (struct meta*)((void*)arena + offset);
	meta -> arena_offset = offset;
	meta -> free = NULL;
	meta -> block_size = block_size;

	return meta;
}

static size_t apply_for_meta(struct arena *arena, size_t block_size) {
	size_t offset = atom_l_n(&(arena -> memory_used)) + sizeof(struct arena);
	size_t step;
	atom_keep_ce_n(&(arena -> memory_used), &offset, step,
		step = offset + block_size + sizeof(struct meta);
		if (step > ARENA_SIZE) {
			offset = 0; break;
		});
	return offset;
}

static intptr_t apply_for_mmap(size_t block_size) {
	if (block_size > G) return 0;

	intptr_t develop, addr;

	develop = atom_l_n(&developing_dist[1]);
	intptr_t end = develop + DISTRICT_SIZE;
	if (atom_l_n(&tail) +  block_size >= end) {
		if (atom_ce_n(&developing_dist[1], &develop, end)) {
#ifdef __LINUX__
			madvise(developing_dist[1], DISTRICT_SIZE, MADV_HUGEPAGE);
#endif
		}
	}
	atom_keep_ce_n(&tail, &addr, addr + block_size,
		develop = atom_l_n(&developing_dist[1]);
		intptr_t end = develop + DISTRICT_SIZE;
		if (atom_l_n(&tail) +  block_size >= end) {
			if (atom_ce_n(&developing_dist[1], &develop, end)) {
#ifdef __LINUX__
				madvise(developing_dist[1], DISTRICT_SIZE, MADV_HUGEPAGE);
#endif
			}
		}
		addr = atom_l_n(&tail););

	return addr;
}

static void free_arena(struct arena *arena, int index) {
	struct arena *iter = atom_l_n(&base[index]);
	struct arena *next, *tmp;
	atom_keep_ce(&(iter -> next), &arena, &(arena -> next),
		while (atom_l_n(&(iter -> next)) != arena) {
			__atomic_exchange(&iter, &(iter -> next), &next, __ATOMIC_RELAXED);
			if (iter == arena) {
				iter = next;
				if (atom_l_n(&(iter -> next)) == NULL) break;
			}
		});
	int c = 0;
	iter = (struct arena*)idle_arena;
	if (atom_l_n(&idle_arena) == 0) {
		intptr_t i = (intptr_t)iter;
		if (atom_ce_n(&idle_arena, &i, (intptr_t)arena))
			return;
	}
	while(true) {
		if (c <= 10) {
			if ((next = atom_l_n(&(iter -> next))) == NULL || next > arena) {
				arena -> next = next;
				if (atom_ce_n(&(iter -> next), &next, arena)) break;
			} else {
				__atomic_exchange(&iter, &(iter -> next), &tmp, __ATOMIC_RELAXED);
				c++;
				if (iter != next) {
					iter = tmp;
					c--;
				}
				if (atom_l_n(&(iter -> memory_used)) != ARENA_SIZE) {
					iter = (struct arena *)atom_l_n(&idle_arena);
					c = 0;
				}
			}
		} else {
			if (atom_l_n(&(arena -> memory_used)) != ARENA_SIZE)
				break;
			madvise(arena, ARENA_SIZE, MADV_DONTNEED);
			if ((next = atom_l_n(&(iter -> next))) == NULL) break;
			__atomic_exchange(&iter, &(iter -> next), NULL, __ATOMIC_RELAXED);
			c++;
			if (iter != next)
				break;
			arena = iter;
		}
	}

	return;

}

static enum meta_type find_meta_type(size_t byte) {

	if (byte <= 1*M)
		return unsaturate;
	if (byte <= 2*M)
		return saturate;
	return oversaturate;

}

static int find_size_base(size_t size) {
	return log_2(next_pow_2(size));
}

static inline void* get_ptr(intptr_t addr) {
	return (void*)0 +addr;
}

static void data_cpy(void* dst, void* src) {
	size_t byte = (malloc_size(src) > malloc_size(dst)) ? malloc_size(dst) : malloc_size(src);
	size_t c64, c32, c16;
	byte -= (c64 = byte / 8);
	byte -= (c32 = byte / 4);
	byte -= (c16 = byte / 2);
	while (c64--) *(long long int*)(dst++) = *(long long int*)(src++);
	while (c32--) *(long int*)(dst++) = *(long int*)(src++);
	while (c16--) *(int*)(dst++) = *(int*)(src++);
	while (byte--) *(char*)(dst++) = *(char*)(src++);
	return;
}

static size_t next_pow_2(size_t v) {
	v--;
	v |= v >> 1;
	v |= v >> 2;
	v |= v >> 4;
	v |= v >> 8;
	v |= v >> 16;
	v++;
	return v += (v == 0);
}

static int log_2(size_t v) {
	static const int MultiplyDeBruijnBitPosition2[32] = {
		0, 1, 28, 2, 29, 14, 24, 3, 30, 22, 20, 15, 25, 17, 4, 8,
		31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18, 6, 11, 5, 10, 9
	};
	return MultiplyDeBruijnBitPosition2[(v * 0x077CB531U) >> 27];
}