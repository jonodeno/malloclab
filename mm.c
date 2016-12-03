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
    "Eric and Jon",
    /* First member's full name */
    "Eric Li",
    /* First member's email address */
    "ericli2017@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Jonathan Denose",
    /* Second member's email address (leave blank if none) */
    "jonathandenose2018@u.northwestern.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/*Basic constants and macros*/
#define WSIZE 4 /*word and header/footer size (bytes)*/
#define DSIZE 8 /*double word size (bytes)*/
#define CHUNKSIZE (1<<12)/*Extend the heap by this amount (4096 bytes)*/

#define MAX(x,y) ((x)>(y)?(x):(y))

/*pack a size and allocated bit into a word
this returns a value that can be stored in a header or footer*/
#define PACK(size,alloc) ((size)|(alloc))

/*read and write a word at address pointed to by void pointer p
GET - returns the value of the word referenced by p
PUT - stores val in the word pointed at by p*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p) = (val))

/*read the size and allocated fields from address p*/
#define GET_SIZE(p) (GET(p) & ~0x7)/*returns the size bits*/
#define GET_ALLOC(p) (GET(p) & 0X1)/*returns the bit that shows 
				     whether or not allocated*/
/*given a block pointer, compute its header and footer addresses*/
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*given block ptr bp, compute the address of next and previous blocks*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static void *heap_listp;/*starting heap address*/
static void *prologue;/*prologue block signals start of heap*/
static int alloc_count=0;/*counts the number of allocated blocks in the heap*/

/*******HEAP CHECKER*******/
int mm_check(void *bp)
{
  /*check if the pointer address is too large*/
  if(bp > mem_heap_hi()){
    printf("pointer address too high\n");  
  }
  else if(bp<mem_heap_lo()){
    printf("pointer address too low\n");
  }
  else if(HDRP(bp)<FTRP(PREV_BLKP(bp))){
      printf("current block is overlapping previous block\n");
    }
 else if(FTRP(bp)>HDRP(NEXT_BLKP(bp))){
	printf("current block is overlapping next block or running off heap\n");
      }

  if(!GET_ALLOC(bp))//check if an allocated block has allocated bit set after malloc
    printf("current block does not have allocate bit set\n");
  return alloc_count;
}

/***********HELPER FUNCTIONS***************/
/*boundary tag coalescing function*/
static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
  
  if(prev_alloc && next_alloc){      /*case 1: prev and next are allocated*/
      return bp; 
  }
  else if(prev_alloc && !next_alloc){/*case 2: prev allocated, next free*/
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
  }
  else if(!prev_alloc && next_alloc){/*case 3: prev free, next allocated*/
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
    bp = PREV_BLKP(bp);
  }
  else{                              /*case 4:prev and next are free*/
    size += GET_SIZE(HDRP(PREV_BLKP(bp)))+ GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
    PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
    bp = PREV_BLKP(bp);
  }
  return bp;
}

/*extend_heap - extends the heap with a new free block*/
static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;
  /*allocate an even number of words to maintain alignment*/
  size = (words%2) ? (words+1)* WSIZE : words*WSIZE;
  /*this will fail if we are trying to shrink the stack 
    or if extending exceeds the max address*/
  if((long)(bp=mem_sbrk(size))==-1)
    return NULL;
  /*initialize a free block header/footer and the epilogue header*/
  PUT(HDRP(bp),PACK(size,0));/*free block header*/
  PUT(FTRP(bp),PACK(size,0));/*free block footer*/
  PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));/*new epilogue header*/
  //  mm_check(bp);
  /*coalesce if the previous block was free*/
  return coalesce(bp);
}

static void *find_fit(size_t asize)
{
  /*fit first search*/
  void *bp;
  for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0;bp = NEXT_BLKP(bp)){
    if(!GET_ALLOC(HDRP(bp))&&(asize <= GET_SIZE(HDRP(bp)))){
      return bp;
    }
  }
  return NULL; /*no fit*/
}

static void place(void *bp, size_t asize){
  alloc_count++;
  size_t csize = GET_SIZE(HDRP(bp));

  if ((csize - asize) >= (2*DSIZE)){
    PUT(HDRP(bp),PACK(asize,1));
    PUT(FTRP(bp),PACK(asize,1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp),PACK(csize-asize,0));
    PUT(FTRP(bp),PACK(csize-asize,0));}
  else {
    PUT(HDRP(bp),PACK(csize,1));
    PUT(FTRP(bp),PACK(csize,1));}}

/*************FUNCTIONS TO BE GRADED************/
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
  heap_listp = mem_sbrk(4*WSIZE);
  /*create the initial empty heap*/
  if(heap_listp==(void*)-1)
    return -1;
  PUT(heap_listp,0);                         /*alignment padding*/
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1));/*prologue header*/
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1));/*prologue footer*/
  PUT(heap_listp + (3*WSIZE), PACK(0,1));    /*epilogue header*/
  heap_listp += (2*WSIZE);
  prologue = heap_listp;
  /*extend the empty heap with a free block of CHUNKSIZE bites*/
  if(extend_heap(CHUNKSIZE/WSIZE)== NULL)
    return -1; 
  return 0;
}

/* 
 * mm_malloc - Allocate a block from the free list
 */
void *mm_malloc(size_t size)
{
  size_t asize;/*adjusted block size*/
  size_t extendsize;/*amount to extend heap if no fit*/
  char *bp;
  /*ignore spurious requests*/
  if(size==0)
    return NULL;
  /*adjust block size to include overhead and alignment reqs*/
  if(size <= DSIZE)
    asize = 2*DSIZE;
  else
    asize = DSIZE*((size+(DSIZE)+(DSIZE-1))/DSIZE);
  /*search the free list for a fit*/
  if((bp = find_fit(asize)) != NULL){
  place(bp,asize);
    return bp;}
  /*no fit found. get more memory and place the block*/
  extendsize = MAX(asize,CHUNKSIZE);
  if((bp = extend_heap(extendsize/WSIZE))==NULL)
    return NULL;
  place(bp,asize);
  // mm_check(bp);
  return bp;}

   /*
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);*/


/*
 * mm_free - frees a block and uses coalescing to merge 
 it with any adjacent blocks in constant time
 */
void mm_free(void *ptr)
{
  /*mm_check(ptr);*/
  size_t size = GET_SIZE(HDRP(ptr));

  PUT(HDRP(ptr),PACK(size,0));
  PUT(HDRP(ptr),PACK(size,0));
  coalesce(ptr);
}

/*
 * mm_realloc - there are three constraints
if ptr is null this is a call to malloc
if size is equal to zero the call is equivalent to free
if ptr is not null change the size of the memory block pointed
to by ptr
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t newSize;
    size_t oldSize = GET_SIZE(oldptr);
   
    if (ptr == NULL){//call to malloc
      newptr = mm_malloc(size);
      return newptr;
     }
    
    if(size == 0){//call to free
      mm_free(oldptr);
      return oldptr;
      }
    //otherwise resize the block
    /*if(oldSize > size){//old block is too small to hold size
      //PUT(HDRP(oldptr),PACK(size,1));
      newptr = mm_malloc(size);
      memcpy(newptr,oldptr,GET_SIZE(newptr));
      mm_free(oldptr)
    }*/
    /* if(oldSize<size){//not enough space in old size
      newptr = mm_malloc(size);
      newptr = memcpy(newptr,oldptr,oldSize);//copy ove what you can from oldptr
      mm_free(oldptr);
      return newptr;
    }
    newptr = mm_malloc(size);
    newptr = memcpy(newptr,oldptr,size);
    mm_free(oldptr);
    return newptr;*/
      copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
      if (size < copySize)
      copySize = size;
    newptr = memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
	












