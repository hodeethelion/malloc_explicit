/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "3조",
    /* First member's full name */
    "Hojun Lee",
    /* First member's email address */
    "tlsghk8619@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/* MAKING MANUALLY */
#define WSIZE 4 /*word 혹은 header/
 footer 사이즈 (바이트)*/
#define DSIZE 8 /* Double word 사이즈 (바이트 )*/
#define CHUNKSIZE (1<<12) /*1을 왼쪽으로 12번 이동한 것*/
#define MAX(x,y) ((x)>(y)? (x):(y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int*)(p))
#define PUT(p, val) (*(unsigned int*)(p)=(val))
#define GET_SIZE(p) (GET(p) & ~0x7) // 하위 3비트를 제외함 바이트 단위로 분리함
#define GET_ALLOC(p) (GET(p) & 0x1) // 가장 첫비트를 확인함
#define HDRP(bp)     ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp))- DSIZE) //블록의 크기, 머리글, 바닥글 포함
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


static char *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

int mm_init(void)
{
    /* 4word 빈 공간의 heap을 생성: break point 끌어 올림! */
    if ( (heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1 )
        return -1;
    PUT(heap_listp, 0);/* alignment padding: 패딩 첫번째 패딩을 집어넣는다*/
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /*첫번째 워드를 지난다음 프롤로그 헤더 집어 넣기*/
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /*프롤로그 footer 집어 넣기 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));  /*에필로그 헤더를 집어 넣기*/
    heap_listp += (2*WSIZE); /*첫번째 사용가능한 주소를 의미함. */
   if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}
/* 사이즈를 받아서 extend함 짝수면 word size를 그대로 받아 버림*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    /* Allocate even number of words to maintain alignmens*/
    size = (words%2) ? (words+1) * WSIZE : words *WSIZE; // 짝수면 사이즈에 Wsize곱해서 설정 홀수면 +1함
    if ((long)(bp = mem_sbrk(size)) == -1) //사이즈늘리는 것이 불가능 하다면 -1 NULL 반환 그러니까 한마디로 사이즈를 존나 늘림
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));  //free block header
    PUT(FTRP(bp), PACK(size, 0));  // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // New epilogue header  next blkp에 있는 block point를 알아바줘

    /* 연결해! 일단 연결해 */
    return coalesce(bp);

}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
        return bp;
    }
    // PREV는 alloc 되어있고 next alloc d은 alloc이 안되어있어
    // 
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    else 
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +  
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
    

}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    /* 원래 존재하던 코드
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
    */
   size_t asize; /* adjusted block size*/
   size_t extendsize; /* Amount to extend heap if no fit */
   char *bp;

   /* Ignore spurious requests*/
   if (size == 0)
        return NULL;

    if (size <= DSIZE) // DSIZE double word의 size 그니까 size가 작으면 최소한 16은 할당해줘야 된다
        asize = 2*DSIZE;
    else 
    // 사이즈가 좀 크다면 
        asize = DSIZE *( (size+ (DSIZE)+ (DSIZE-1) ) / DSIZE);
    
    /* SEarch the free list for a fit*/
    if ((bp= find_fit(asize)) != NULL){
        // 만약 fit한게 있다면 place를 해라 
        place(bp, asize);
        return bp;
    }
    /* no fit found. Get more memory and place the block*/
    extendsize = MAX(asize, CHUNKSIZE); // chunk아니면 asize 중에 큰 것을
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) // 그 만큼 extend 해라 그리고 bp에 반환해 bp를
        return NULL;
    place(bp, asize);
    return bp;

}

static void *find_fit(size_t asize)
{
    /* first fit search try 1*/
    // void *bp = NEXT_BLKP(heap_listp);
    // // 여기서 
    // while(GET_SIZE(HDRP(bp))>0)
    // {
    //     if(!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) //allocation이 아니고 사이즈의 asize보다 크거나 같다면
    //         return bp;
    //     bp = NEXT_BLKP(bp);
    // }

    // return NULL; // no fit

    void *bp;
    for (bp= heap_listp; GET_SIZE(HDRP(bp))>0 ; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    return NULL;

}

static void place(void *bp, size_t asize)
{   // 원래 있던 사이즈를 의미함
    size_t csize = GET_SIZE(HDRP(bp));
    // split and allocation 나누고 alloc을함
    if((csize - asize) > (2*DSIZE))
    {   /* 1. HEADER 2. FOOTER  다음 꺼 header and footer. */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK((csize-asize), 0));
        PUT(FTRP(bp), PACK((csize-asize), 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) // 무엇을 하고 싶은 함수 인지 ? --> ptr로 지금 가르키는 것을 다른 곳에다가 옮기고 싶은 것
{
    // void *oldptr = ptr;
    // void *newptr;
    // size_t copySize;
    
    // newptr = mm_malloc(size);
    // if (newptr == NULL)
    //   return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    // if (size < copySize)
    //   copySize = size;
    // memcpy(newptr, oldptr, copySize);
    // mm_free(oldptr);
    // return newptr;

    // change a little
    void *oldptr = ptr; //예전 포인터는 현재 포인터
    void *newptr; // 새로운 포인터 설정
    size_t copySize; // 사이즈 설정
    
    newptr = mm_malloc(size); //새로운 사이즈 할당
    if (newptr == NULL) // new ptr 가 없으면 불가능
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr)); // 예전 포인터에서 사이즈를 갖고와
    if (size < copySize) //만약 현재 사이즈가 크다면
    {
        copySize = size; //copysize에다가 현재 사이즈를 가지고 와
    }
    memcpy(newptr, oldptr, copySize); // 새로운 포인터에다가 예전 복사할 메모리를 갖고 있는 포인터 복사할 데이터의 값
    /*1인자. 복사 받을 메모리를 가리키는 포인터, 2. 복사할 메모리를 가리키고 있는 포인터 */
    mm_free(oldptr); // 예전 포인터를 없애줘
    // 새로운 포인터를 반환해
    return newptr;


 /*   size_t oldsize = GET_SIZE(HDRP(ptr));
    size_t asize;
    void *newptr;


    if(ptr == NULL) return mm_malloc(size);
    else if(size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    if(size <= DSIZE) asize = 2 * DSIZE;
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    
    if(asize <= oldsize)
    {
        place(ptr, asize);
        return ptr;
    }
    else
    {
        newptr = mm_malloc(size);
        memcpy(newptr, ptr, oldsize);
        mm_free(ptr);
        return newptr;
    }
*/



}
