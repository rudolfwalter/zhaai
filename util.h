#ifndef UTIL_H
#define UTIL_H
#include <stddef.h>

#define PP_STR1(x) #x
#define PP_STR(x) PP_STR1(x)

#define PP_CONCAT1(x,y) x ## y
#define PP_CONCAT(x,y) PP_CONCAT1(x,y)

#define GS_ASSERT(cond) enum { PP_CONCAT(gs_assert_line_, __LINE__) = 1/(!!(cond)) }

#ifndef int8_t
typedef signed   char       int8_t;
#endif
#ifndef uint8_t
typedef unsigned char      uint8_t;
#endif
#ifndef int16_t
typedef signed   short      int16_t;
#endif
#ifndef uint16_t
typedef unsigned short     uint16_t;
#endif
#ifndef int32_t
typedef signed   int        int32_t;
#endif
#ifndef uint32_t
typedef unsigned int       uint32_t;
#endif
#ifndef int64_t
typedef ptrdiff_t           int64_t;
#endif
#ifndef uint64_t
typedef size_t             uint64_t;
#endif

GS_ASSERT(sizeof( int8_t ) == 1);
GS_ASSERT(sizeof(uint8_t ) == 1);
GS_ASSERT(sizeof( int16_t) == 2);
GS_ASSERT(sizeof(uint16_t) == 2);
GS_ASSERT(sizeof( int32_t) == 4);
GS_ASSERT(sizeof(uint32_t) == 4);
GS_ASSERT(sizeof( int64_t) == 8);
GS_ASSERT(sizeof(uint64_t) == 8);

#endif

