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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

int mm_init(void);
static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
void mm_free(void *bp);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_realloc(void *bp, size_t size);

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 // word and header footer 사이즈를 byte로
#define DSIZE 8 // double word size를 byte로
#define CHUNKSIZE (1<<12) // heap을 늘릴 때 4kb 분량으로 늘림.

#define MAX(x,y) ((x)>(y) ? (x) : (y)) // x,y 중 큰 값을 가진다.

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산), 헤더에서 써야하기 때문에 생성.
#define PACK(size,alloc) ((size)|(alloc)) // alloc : 가용여부 (ex.000) / size : block size를 의미 -> 합치면 온전한 주소가 나옴

/* address p위치에 words를 read와 write 한다.*/
#define GET(p) (*(unsigned int*)(p)) // 포인트를 써서 p를 참조. 주소와 값(값에는 다른 블록의 주소를 담는다.)을 알 수 있다. 다른 블록을 가리키거나 이동할 때 쓸 수 있음.
#define PUT(p,val) (*(unsigned int*)(p)=(val)) // 블록의 값을 담는다. 위치를 담아야 나중에 header나 footer를 읽어서 이동 혹은 연결할 수 있음

/* address p위치로부터 size를 읽고 field를 할당 */
#define GET_SIZE(p) (GET(p) & ~0x7) // '~'은 역수니까 11111000이 됨. 비트 연산하면 000 앞에거만 가져올 수 있음. 즉, 헤더에서 블록 size만 가져오겠다.
#define GET_ALLOC(p) (GET(p) & 0x1) // 00000001이 됨. 헤더에서 가용여부만 가져오겠다.

/* given block ptr bp, header와 footer의 주소를 계산 */
#define HDRP(bp) ((char*)(bp) - WSIZE) // bp가 어디에있던 상관없이 WSIZE 앞에 위치한다.
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 헤더의 끝 지점부터 GET SIZE(블록의 사이즈)만큼 더한 다음 word를 2번빼는게(그 뒤 블록의 헤드에서 앞으로 2번) footer의 시작 위치가 된다.


/* GIVEN block ptr bp, 이전 블록과 다음 블록의 주소를 계산 */
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) // 그 다음 블록의 bp 위치로 이동한다.(bp에서 해당 블록의 크기만큼 이동 -> 그 다음 블록의 헤더 뒤로 감.)
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 그 전 블록의 bp위치로 이동.(이전 블록 footer로 이동하면 그 전 블록의 사이즈를 알 수 있으니 그만큼 그 전으로 이동.)

static char *heap_listp;
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* create : 초기의 빈 heap 할당(mem_sbrk) */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)    
        return -1;

    PUT(heap_listp, 0); // 패딩 생성
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); // prologue header 생성
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); // prologue footer 생성
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); // epilogue block header 생성
    heap_listp += (2*WSIZE); // prologue header와 footer 사이로 포인터를 옮김. header 뒤 위치. 다른 블록으로 가기 위해?

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){ // extend heap을 통해 시작할 때 한번 heap을 늘려줌. 늘리는 양은 상관없다.
        return -1;
    }
    return 0;
}

// 새 가용 블록으로 힙을 확장
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    /* alignment 유지를 위해 짝수 개수의 words를 할당*/
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 홀수면 앞, 짝수면 뒤가 나옴
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    // free block header와 footer를 init하고 epilogue header를 init
    PUT(HDRP(bp), PACK(size, 0)); // free block header 생성 / regular block의 총합의 첫번째 부분. 현재 bp위치의 한 칸 앞에 헤더를 생성
    PUT(FTRP(bp), PACK(size, 0)); // free block footer 생성 / regular block의 마지막 부분
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // block을 추가했으니 epilogue header를 새롭게 위치 조정해줌
    // HDRP : 1word 뒤에 있는 것을 지칭.
    // bp를 header에서 읽은 사이즈만큼 이동하고, 앞으로 한칸 간다. 그 위치가 결국 늘린 블록 끝에서 한칸 간것이기 때문에, epilogue header 위치가 됨

    // 만약 previous block이 free 상태라면 병합(coalesce)
    return coalesce(bp);

}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
    size_t asize; // block 사이즈 조정
    size_t extendsize; // heap에 맞는 fit이 없으면 확장하기 위한 사이즈
    char *bp;

    /* 거짓된 요청 무시 */
    if (size == 0) return NULL;

    /* overhead, alignment 요청 포함해서 블록 사이즈 조정 */
    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        // size보다 클 때, 블록이 가질 수 있는 크기 중, 최적회된 크기로 재조정
        asize = DSIZE * ((size + (DSIZE)+(DSIZE-1)) / DSIZE);
    }
    // fit에 맞는 free 리스트를 찾는다.
    if ((bp = find_fit(asize)) != NULL){
        place(bp,asize);
        return bp;
    }
    /* fit에 맞는게 없는 경우, 메모리를 더 가져와 block을 위치시킴 */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp=extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // 어느 시점에 있는 bp를 인자로 받음
    size_t size = GET_SIZE(HDRP(bp)); // 얼마만큼 free를 해야하는지
    PUT(HDRP(bp), PACK(size,0)); // header free -> 가용상태로 만들기
    PUT(FTRP(bp), PACK(size,0)); // footer free -> 가용상태로 만들기
    coalesce(bp);
}
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈 확인

    // case 1
    if (prev_alloc && next_alloc){
        return bp;
    }
    // case 2
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // header 갱신 (더 큰 크기로 PUT)
        PUT(FTRP(bp), PACK(size,0)); // footer 갱신
    }
    // case 3
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    // case 4
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *find_fit(size_t asize){
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        // for문이 계속 돌면 epliogue header까지 간다. epliogue header는 0이므로 끝까지 가면 종료됨
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ // 이 블록이 가용상태이고, 내가 갖고있는 asize를 담을 수 있다면
            return bp; // 내가 넣을 수 있는 블록만 찾으면 되기 때문에, 바로 리턴
        }
    }
    return NULL; // NULL 리턴 시, fit에 맞는 block이 없는 것
}

static void place(void *bp, size_t asize){
    // 요청한 블록을 가용 블록의 시작 부분에 배치한다. 
    // 나머지 부분의 크기가 최소 블록의 크기와 같거나 큰 경우에만 분할하는 함수
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize-asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else{
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size) // bp : 크기를 조정할 블록의 위치, size : 요청 사이즈
{
    // 요청 사이즈가 0보다 작거나 같다면 free 상태로 만들고 0을 리턴해줌
    if (size <= 0){
        mm_free(bp);
        return 0;
    }
    // 위치(bp)가 없다면 malloc을 통해 새로 생성해줌 (예외처리의 일종)
    if (bp == NULL){
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);
    if(newp == NULL){
        return 0;
    }
    // 요청 사이즈가 기존 사이즈보다 작으면 요청 사이즈만큼 데이터를 잘라서 옮겨준다.
    size_t oldsize = GET_SIZE(HDRP(bp));
    if (size < oldsize){
        oldsize = size;
    }
    // 블록 내의 데이터를 옮기기 위한 함수
    memcpy(newp, bp, oldsize);
    // 기존 블록 반환
    mm_free(bp);
    return newp;
}














