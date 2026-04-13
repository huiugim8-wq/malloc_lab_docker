/*
 * mm-naive.c - 가장 빠르지만 메모리 효율이 가장 낮은 malloc 패키지
 *
 * 이 단순한 접근 방식에서는, brk 포인터를 단순히 증가시켜
 * 블록을 할당한다. 블록은 순수 payload만 가진다.
 * header나 footer는 없다. 블록은 병합(coalescing)되거나
 * 재사용되지 않는다. realloc은 mm_malloc과 mm_free를
 * 직접 사용하는 방식으로 구현되어 있다.
 *
 * NOTE TO STUDENTS: 이 헤더 주석을 여러분의 구현 방식에 대한
 * 높은 수준의 설명으로 교체하라.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: 시작하기 전에 아래 struct에
 * 팀 정보를 반드시 입력하라.
 ********************************************************/
team_t team = {
    /* 팀 이름 */
    "5team",
    /* 첫 번째 팀원의 이름 */
    "Harry potter",
    /* 첫 번째 팀원의 이메일 */
    "hurry@cs.cmu.edu",
    /* 두 번째 팀원의 이름 (없으면 빈칸) */
    "",
    /* 두 번째 팀원의 이메일 (없으면 빈칸) */
    ""};

/* 단일 워드(4바이트) 또는 더블 워드(8바이트) 정렬 */
#define ALIGNMENT 8

/* size를 ALIGNMENT의 배수로 올림 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
//0x7 = 0000 0111 
// '~'는 비트 반전 연산자(NOT)
// 1111 1000 -> 7앞을 1로만들기

// sizeof byte 단위크기를 반환
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/* 
size가 18일 경우 18+7 = 25(11001)
 11001
&11111000 (7)
--------
 11000 (24)
 & 연사자니까 둘다 1일때만
*/

//주소계산
#define WORDSIZE 4
#define DOUBLEWORDSIZE 8
#define CHUNKSIZE (1<<12) //heap을 한 번 확장할 때 기본으로 늘릴 크기 2^12 = 4096

// 힙 확장시 작은요청, 큰 요청 조건부로 하려고
#define MAX(x, y) ((x) > (y) ? (x) : (y))


// header, footer에 저장할 하나의 값 - 한 워드에 저장

#define PACK(size, alloc) ((size) |(alloc))

//header, footer 구하기
// bp= block pointer (payload 시작주소) return char *bp
// *char는 문자를 위한 포인터가 아닌, 1바이트 단위 주소 계산을 위한 포인터
#define HEADERPOINT(bp) ((char *)(bp) - WORDSIZE) 
#define FOOTERPOINT(bp) ((char *)(bp) + GET_SIZE(HEADERPOINT(bp))- DOUBLEWORDSIZE)

//메모리 읽기-쓰기
// p는 메모리주소, 주소의 값value
// char *         : 주소를 1바이트 단위로 계산하려고 씀
// unsigned int * : 그 주소의 4바이트 값을 정수로 읽고 쓰려고 씀
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))


//header에서 정보분리(size | alloc)
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

//다음/이전블록이동
#define NEXT_BP(bp) ((char*)(bp) + GET_SIZE(HEADERPOINT(bp)))
#define PREV_BP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DOUBLEWORDSIZE)))


static char *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
/*
 * mm_init - malloc 패키지 초기화 함수
 */
int mm_init(void)
{
    // 비어있는 초기 heap 생성
    if((heap_listp = mem_sbrk(4*WORDSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WORDSIZE), PACK(DOUBLEWORDSIZE,1));
    PUT(heap_listp + (2*WORDSIZE), PACK(DOUBLEWORDSIZE,1));
    PUT(heap_listp + (3*WORDSIZE), PACK(0, 1));
    heap_listp += (2*WORDSIZE);

    //CHUNKSIZE bytes 만큼 비어있는 free block으로 확장하기
    //extend_heap 함수는 coalesce 그값을 반환값을로 전달
    if(extend_heap(CHUNKSIZE/WORDSIZE) == NULL) 
        return -1;

    return 0;
}

/*
 * mm_malloc - brk 포인터를 증가시켜 블록을 할당
 *     항상 ALIGNMENT 배수 크기의 블록을 할당한다.
 */
void *mm_malloc(size_t size)
{
    size_t asize; 
    size_t extendsize;
    char *bp;

    if (size == 0){
        return NULL;
    }

    if (size <= DOUBLEWORDSIZE){
        asize = 2 * DOUBLEWORDSIZE;

    } 
    else {
        asize = DOUBLEWORDSIZE * ((size + (DOUBLEWORDSIZE) + (DOUBLEWORDSIZE -1))/DOUBLEWORDSIZE);
    }
    //find_fit 함수 구현
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WORDSIZE)) == NULL){
        return NULL;
    }
    //place 함수 구현
    place(bp, asize);
    return bp;
}

// heap 초기화시 free공간 생성, heap 추가 공간 요청시
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // 정렬을 유지하기 위해 word를 짝수 num 으로 만들기
    size = (words % 2) ? (words+1) * WORDSIZE : words * WORDSIZE;
    // heap공간 늘어났는지 확인 아니라면(-1 실패) NULL로 종료
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // 새 free block의 header/footer를 기록하고,
    // 그 다음 위치에 새 epilogue header를 세운다
    PUT(HEADERPOINT(bp), PACK(size, 0)); //free block header
    PUT(FOOTERPOINT(bp), PACK(size, 0));
    PUT(HEADERPOINT(NEXT_BP(bp)), PACK(0,1));

    // 이전 블록이 free면 coalesce
    return coalesce(bp);
}
/*
 * mm_free - 블록 해제 (아무 동작도 하지 않음)
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HEADERPOINT(ptr));
    //현재 블록을 free로 표시
    PUT(HEADERPOINT(ptr), PACK(size, 0));
    PUT(FOOTERPOINT(ptr), PACK(size, 0));
    //병합이 필요한지는 coalesce에서 분기
    coalesce(ptr);
}

static void *coalesce(void *bp){
    // 이전 블록 footer alloc 확인
    int prev_alloc = GET_ALLOC(FOOTERPOINT(PREV_BP(bp)));
    // 다음블록 header의 alloc확인 
    int next_alloc = GET_ALLOC(HEADERPOINT(NEXT_BP(bp)));
    // 현재블록크기 읽기
    size_t size = GET_SIZE(HEADERPOINT(bp));

    //case 1 앞, 뒤블럭 둘다 free블럭 이 아닐 때 (allocated)
    if (prev_alloc && next_alloc) {
        return bp;
    }

    //case 2 뒤 블럭만 free블럭일 때
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HEADERPOINT(NEXT_BP(bp)));
        PUT(HEADERPOINT(bp), PACK(size, 0));
        PUT(FOOTERPOINT(bp), PACK(size, 0));
    }

    //case 3 앞 블럭만 free블럭일 때 
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HEADERPOINT(PREV_BP(bp)));
        PUT(FOOTERPOINT(bp), PACK(size, 0));
        PUT(HEADERPOINT(PREV_BP(bp)), PACK(size, 0));
        bp = PREV_BP(bp);
    }

    //case 4 앞, 뒤 블럭만 free블럭일 때
    else {
        size += GET_SIZE(HEADERPOINT(PREV_BP(bp)));
        size += GET_SIZE(FOOTERPOINT(NEXT_BP(bp)));
        PUT(HEADERPOINT(PREV_BP(bp)), PACK(size, 0));
        PUT(FOOTERPOINT(NEXT_BP(bp)), PACK(size, 0));
        bp = PREV_BP(bp);
    }

    return bp;
}

/*
 * mm_realloc - mm_malloc과 mm_free를 이용해서 단순 구현
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *find_fit(size_t asize){
    void *bp;
    
    for(bp = heap_listp; GET_SIZE(HEADERPOINT(bp)) > 0; bp = NEXT_BP(bp)){
        if (!GET_ALLOC(HEADERPOINT(bp)) && (asize <= GET_SIZE(HEADERPOINT(bp)))){
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HEADERPOINT(bp));

    if((csize - asize) >= (2*DOUBLEWORDSIZE)){
        PUT(HEADERPOINT(bp), PACK(asize,  1));
        PUT(FOOTERPOINT(bp), PACK(asize,  1));
        bp = NEXT_BP(bp);
        PUT(HEADERPOINT(bp), PACK(csize - asize, 0));
        PUT(FOOTERPOINT(bp), PACK(csize - asize, 0));
    }

    else {
        PUT(HEADERPOINT(bp), PACK(csize,1));
        PUT(FOOTERPOINT(bp), PACK(csize,1));
    }
}
// /*
//  * mm-naive.c - The fastest, least memory-efficient malloc package.
//  *
//  * In this naive approach, a block is allocated by simply incrementing
//  * the brk pointer.  A block is pure payload. There are no headers or
//  * footers.  Blocks are never coalesced or reused. Realloc is
//  * implemented directly using mm_malloc and mm_free.
//  *
//  * NOTE TO STUDENTS: Replace this header comment with your own header
//  * comment that gives a high level description of your solution.
//  */
// #include <stdio.h>
// #include <stdlib.h>
// #include <assert.h>
// #include <unistd.h>
// #include <string.h>

// #include "mm.h"
// #include "memlib.h"

// /*********************************************************
//  * NOTE TO STUDENTS: Before you do anything else, please
//  * provide your team information in the following struct.
//  ********************************************************/
// team_t team = {
//     /* Team name */
//     "ateam",
//     /* First member's full name */
//     "Harry Bovik",
//     /* First member's email address */
//     "bovik@cs.cmu.edu",
//     /* Second member's full name (leave blank if none) */
//     "",
//     /* Second member's email address (leave blank if none) */
//     ""};

// /* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// /*
//  * mm_init - initialize the malloc package.
//  */
// int mm_init(void)
// {
//     return 0;
// }

// /*
//  * mm_malloc - Allocate a block by incrementing the brk pointer.
//  *     Always allocate a block whose size is a multiple of the alignment.
//  */
// void *mm_malloc(size_t size)
// {
//     int newsize = ALIGN(size + SIZE_T_SIZE);
//     void *p = mem_sbrk(newsize);
//     if (p == (void *)-1)
//         return NULL;
//     else
//     {
//         *(size_t *)p = size;
//         return (void *)((char *)p + SIZE_T_SIZE);
//     }
// }

// /*
//  * mm_free - Freeing a block does nothing.
//  */
// void mm_free(void *ptr)
// {
// }

// /*
//  * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
//  */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;

//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//         return NULL;
//     copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//     if (size < copySize)
//         copySize = size;
//     memcpy(newptr, oldptr, copySize);
//     mm_free(oldptr);
//     return newptr;
// }