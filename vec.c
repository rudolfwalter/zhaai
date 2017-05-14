/*
	Expects VEC_TYPE to be the type parameter.
	Optionally, VEC_TYPE_NAME can be defined, if VEC_TYPE is not a valid identifier name (e.g. contains stars).
*/

#ifndef VEC_TYPE
#error VEC_TYPE generic argument must be defined when including vec.c.
#endif

#ifndef VEC_TYPE_NAME
#define VEC_TYPE_NAME VEC_TYPE
#endif

#define VEC_STRUCT       PP_CONCAT(vec_,         VEC_TYPE_NAME)
#define VEC_MAKE_FUNC    PP_CONCAT(VEC_STRUCT, _make)
#define VEC_DESTROY_FUNC PP_CONCAT(VEC_STRUCT, _destroy)
#define VEC_PUSH_FUNC    PP_CONCAT(VEC_STRUCT, _push)
#define VEC_POP_FUNC     PP_CONCAT(VEC_STRUCT, _pop)
#define VEC_SHRINK_FUNC  PP_CONCAT(VEC_STRUCT, _shrink)

struct VEC_STRUCT {
	VEC_TYPE* v;
	size_t n;
	size_t sz;
};

struct VEC_STRUCT VEC_MAKE_FUNC(size_t sz)
{
	struct VEC_STRUCT v;
	v.sz = sz;
	v.v = malloc(sizeof(VEC_TYPE) * v.sz);
	v.n = 0;
	return v;
}

void VEC_DESTROY_FUNC(struct VEC_STRUCT* v)
{
	free(v->v);
}

void VEC_PUSH_FUNC(struct VEC_STRUCT* v, VEC_TYPE val)
{
	if (v->n == v->sz) {
		v->sz++;
		v->sz *= 2;
		v->v = realloc(v->v, sizeof(VEC_TYPE) * v->sz);
	}

	v->v[v->n++] = val;
}

VEC_TYPE VEC_POP_FUNC(struct VEC_STRUCT* v)
{
	return v->v[--v->n];
}

void VEC_SHRINK_FUNC(struct VEC_STRUCT* v)
{
	if (v->n == v->sz) return;

	v->sz = v->n;
	v->v = realloc(v->v, sizeof(VEC_TYPE) * v->sz);
}

#undef VEC_STRUCT
#undef VEC_MAKE_FUNC
#undef VEC_DESTROY_FUNC
#undef VEC_PUSH_FUNC
#undef VEC_POP_FUNC
#undef VEC_SHRINK_FUNC

#undef VEC_TYPE
#undef VEC_TYPE_NAME
