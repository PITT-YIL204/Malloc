/* malloc.h
 * implementations for memory reserve functions
 * Author: Yilin Liu
 */

#ifndef __MALLOC__
#define __MALLOC__

#include <unistd.h>

/* prototypes */
void *malloc(size_t byte);
void free(void* ptr);
void *calloc(size_t num, size_t size);
void *realloc(void *ptr, size_t byte);
size_t malloc_size(void* ptr);
size_t malloc_memory(void);

#endif
