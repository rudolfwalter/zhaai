#ifdef __GNUC__

__attribute__((always_inline))
unsigned bit_ffs(uint64_t x)
{
	return (unsigned) __builtin_ffsll((int64_t) x);
}

#else

#error "TODO: implement bit_ffs() on non-gnu compilers"

#endif
