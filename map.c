/*
	The key type is always void*.
	Expects MAP_TYPE to be the value type parameter.
	Optionally, MAP_TYPE_NAME can be defined. If MAP_TYPE is not a valid
	identifier name (e.g. contains stars), it is also mandatory.
*/

#include <stdlib.h>
#include <assert.h>
#include "util.h"

#ifndef MAP_TYPE
#error MAP_TYPE generic argument must be defined when including map.c.
#endif

#ifndef MAP_TYPE_NAME
#define MAP_TYPE_NAME MAP_TYPE
#endif

#define MAP_STRUCT       PP_CONCAT(map_,        MAP_TYPE_NAME)
#define MAP_BUCKET       PP_CONCAT(map_bucket_, MAP_TYPE_NAME)
#define MAP_OBJ          PP_CONCAT(map_obj_,    MAP_TYPE_NAME)

#define MAP_MAKE_FUNC    PP_CONCAT(MAP_STRUCT, _make)
#define MAP_MAKE_N_FUNC  PP_CONCAT(MAP_STRUCT, _make_buckets_n)
#define MAP_DESTROY_FUNC PP_CONCAT(MAP_STRUCT, _destroy)
#define MAP_REHASH_FUNC  PP_CONCAT(MAP_STRUCT, _rehash)
#define MAP_GET_FUNC     PP_CONCAT(MAP_STRUCT, _get)
#define MAP_ADD_FUNC     PP_CONCAT(MAP_STRUCT, _add)
#define MAP_REMOVE_FUNC  PP_CONCAT(MAP_STRUCT, _remove)


struct MAP_OBJ {
	void* key;
	MAP_TYPE val;
};

struct MAP_BUCKET {
	struct MAP_OBJ inline_obj;
	struct MAP_OBJ* dynamic_obj;
	size_t n;
};

struct MAP_STRUCT {
	struct MAP_BUCKET* buckets;
	size_t buckets_n;
	size_t n;
};

bool MAP_ADD_FUNC(struct MAP_STRUCT* m, void* key, MAP_TYPE val);

struct MAP_STRUCT MAP_MAKE_N_FUNC(size_t buckets_n)
{
	struct MAP_STRUCT m;
	m.n = 0;
	m.buckets_n = buckets_n;
	m.buckets = calloc(m.buckets_n, sizeof(struct MAP_BUCKET));
	
	return m;
}

struct MAP_STRUCT MAP_MAKE_FUNC()
{
	return MAP_MAKE_N_FUNC(7);
}

void MAP_DESTROY_FUNC(struct MAP_STRUCT* m)
{
	size_t i;
	for (i=0; i<m->buckets_n; i++)
		if (m->buckets[i].n > 1)
			free(m->buckets[i].dynamic_obj);
	
	free(m->buckets);
}

void MAP_REHASH_FUNC(struct MAP_STRUCT* m, size_t new_buckets_n)
{
	size_t i, j;
	struct MAP_STRUCT new_m = MAP_MAKE_N_FUNC(new_buckets_n);
	
	for (i=0; i<m->buckets_n; i++) {
		struct MAP_BUCKET* b = &m->buckets[i];
		
		if (b->n > 0) MAP_ADD_FUNC(&new_m, b->inline_obj.key, b->inline_obj.val);
		
		for (j=0; j+1<b->n; j++)
			MAP_ADD_FUNC(&new_m, b->dynamic_obj[j].key, b->dynamic_obj[j].val);
	}
	
	MAP_DESTROY_FUNC(m);
	*m = new_m;
}

MAP_TYPE* MAP_GET_FUNC(struct MAP_STRUCT* m, void* key)
{
	size_t i;
	struct MAP_BUCKET* b = &m->buckets[((size_t) key) % m->buckets_n];
	
	if (b->n == 0) return NULL;
	
	if (b->inline_obj.key == key) return &b->inline_obj.val;
	
	for (i=0; i+1<b->n; i++)
		if (b->dynamic_obj[i].key == key)
			return &b->dynamic_obj[i].val;
	
	return NULL;
}

bool MAP_ADD_FUNC(struct MAP_STRUCT* m, void* key, MAP_TYPE val)
{
	struct MAP_BUCKET* b = &m->buckets[((size_t) key) % m->buckets_n];
	
	MAP_TYPE* p_existing = MAP_GET_FUNC(m, key);
	if (p_existing) {
		*p_existing = val;
		return false;
	}
	
	if (b->n  == 0) {
		b->inline_obj.key = key;
		b->inline_obj.val = val;
	} else {
		b->dynamic_obj = realloc(b->dynamic_obj, (b->n)*sizeof(struct MAP_OBJ)); /*grow by 1*/
		b->dynamic_obj[b->n-1].key = key;
		b->dynamic_obj[b->n-1].val = val;
	}
	
	b->n++;
	m->n++;
	
	if (m->n >= m->buckets_n)
		MAP_REHASH_FUNC(m, (m->buckets_n+1)*2-1);
	
	return true;
}

void MAP_REMOVE_FUNC(struct MAP_STRUCT* m, void* key)
{
	size_t i;
	struct MAP_BUCKET* b = &m->buckets[((size_t) key) % m->buckets_n];
	
	assert(b->n >= 1);
	
	if (b->n > 1) {
		if (b->inline_obj.key == key)
			b->inline_obj = b->dynamic_obj[b->n-2];
		else {
			for (i=0; i+2<b->n; i++)
				if (b->dynamic_obj[i].key == key) {
					b->dynamic_obj[i] = b->dynamic_obj[b->n-2];
					break;
				}
		}
	}
	
	b->n--;
	m->n--;
	
	b->dynamic_obj = realloc(b->dynamic_obj, (b->n-2)*sizeof(struct MAP_OBJ)); /*shrink by 1*/
}

#undef MAP_STRUCT
#undef MAP_BUCKET
#undef MAP_OBJ

#undef MAP_MAKE_FUNC
#undef MAP_MAKE_N_FUNC
#undef MAP_DESTROY_FUNC
#undef MAP_REHASH_FUNC
#undef MAP_GET_FUNC
#undef MAP_ADD_FUNC
#undef MAP_REMOVE_FUNC

#undef MAP_TYPE
#undef MAP_TYPE_NAME
