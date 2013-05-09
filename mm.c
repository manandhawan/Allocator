/*
 * mm.c - The fastest, least memory-efficient malloc package.
 * 
 * Makes use of explicit free lists to keep track of memory. 
 * Two pointers to the beginning and end of the free list are maintained
 * throughout.  The free list is organized according to block size 
 * to enjoy minimal internal fragmentation.  A first-fit method is used, and
 * since the blocks are sorted this implies a best-fitting block every time malloc
 * is called.  If possible, the block is split and re-added to the free list. 
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
    "Absolute",
    /* First member's full name */
    "Manan Dhawan",
    /* First member's email address */
    "201101052@daiict.ac.in",
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

#define WSIZE 4 /* Size of word*/
#define DSIZE 8 /* Size of Double word */
#define CHUNKSIZE (1<<12) /* Initial size of heap for expanding */
#define OVERHEAD 8 /*Extra bytes used by header and footer */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)    ((size) | (alloc))

/* Read and write a word at address p */ 
#define GET(p)                  (*(size_t *)(p)) 
#define PUT(p, val)             (*(size_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)        (GET(p) & ~0x7)
#define GET_ALLOC(p)       (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header */
#define HDRP(bp) ((char *)(bp) - WSIZE)

/* Given block ptr bp, compute address of its footer */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)


/* Given block ptr, compute address of next block */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) -WSIZE))) 

/* Given block ptr, compute address of previous block */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 


static char *heap_listp = NULL;		// Points to the first block
int gminlist = 0;  		// Global first list with free blocks
int gcount = 0;			// Global count of free blocks

static void *extend_heap(size_t words);
static void *first_fit(size_t asize);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void add_free_list(void *bp);
static void remove_free_list(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	if((heap_listp = mem_sbrk(88*WSIZE)) == (void *)-1) //Request 4 words of heap space
		return -1;
	
	PUT(heap_listp, 0);				//Create 4 byte pad

	int i;
	for(i = 2; i < 86; i++) {
		PUT(heap_listp + (i*WSIZE), 0); /* initialize free pointers (one for every increment of 50 bytes*/
	}

	PUT(heap_listp+WSIZE, PACK(43*DSIZE, 1)); 	// Prologue header
   	PUT(heap_listp+(86*WSIZE), PACK(43*DSIZE, 1)); 	// Prologue footer
   	PUT(heap_listp+(87*DSIZE), PACK(0, 1)); 	// Epilogue header
	heap_listp += DSIZE; 
	gminlist = 100; // initialize global_minlist to indicate no free blocks
	gcount = 0;  //set free count to 0 to signify no free blocks.	

	
	if(extend_heap(CHUNKSIZE/WSIZE) == NULL) 	// Extend heap with an initial free block of CHUNKSIZE bytes
		return -1; 

	return 0;

}

static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

	if ((int)(bp = mem_sbrk(size)) == -1)
		return NULL;

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
	PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce to combine neighboring free blocks if possible */
	bp = coalesce(bp);
	return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
   	size_t asize; 		// Adjusted block size 
	size_t extendsize; 	// Amount to extend heap if no fit
	char *bp;

	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment requirements */
	if (size <= DSIZE)
		asize = 2*DSIZE;
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

	/* Search for a free list by first fit */
	if ((bp = first_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
	}

	/* Extend by maximum of asize and CHUNKSIZE if no fit found */
	extendsize = MAX(asize,CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL;
	
	place(bp, asize);
	return bp;
}

static void *first_fit(size_t asize)
{
	void *bp;
	 
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0;bp = NEXT_BLKP(bp))
	{ 
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
			return bp; 
	}
	return NULL;    // No fit found

}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));	// Size of the block to be freed

	/* Reset allocation status to free for header and footer*/
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	
	coalesce(bp);				// Coalesce with neighboring free blocks

}


static void *coalesce(void *bp)
{
	/* Allocation status of previous and next block*/
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	
	size_t size = GET_SIZE(HDRP(bp));		// Size of the current block
	
	if(prev_alloc && next_alloc)			// Case 1: Previous and next blocks are allocated
	{
		add_free_list(bp);
		return bp;
	}
	else if(prev_alloc && !next_alloc)		// Case 2: Previous block is allocated and next block is free
	{
		remove_free_list(NEXT_BLKP(bp));	
		
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));	// Size of the coalesced block
		
		/*Set allocation status to free for header and footer of the coalesced block*/
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));

		add_free_list(bp);
	}
	else if(!prev_alloc && next_alloc)		 // Case 3: Previous block is free and next block is allocated
	{
		remove_free_list(PREV_BLKP(bp));

		size += GET_SIZE(HDRP(PREV_BLKP(bp)));	// Size of the coalesced block
		
		/*Set allocation status to free for header and footer of the coalesced block*/
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
		
		// Set bp to previous block because the header of the coalesced block is now previous block
		bp = PREV_BLKP(bp);

		add_free_list(bp);
	}
	else						// Case 4: Previous and next blocks are free
	{
		remove_free_list(PREV_BLKP(bp));
		remove_free_list(NEXT_BLKP(bp));

		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));	// Size of the coalesced block

		/*Set allocation status to free for header and footer of the coalesced block*/
                PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
                PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
                
                // Set bp to previous block because the header of the coalesced block is now previous block
                bp = PREV_BLKP(bp);

                add_free_list(bp);
	}
	
	return bp;
}

static void place(void *bp, size_t asize)
{
	void *nxt_bp;
	
	size_t csize = GET_SIZE(HDRP(bp));	// Get size of the current free block
	
	if((csize - asize) >= (2*DSIZE))	// If block is large enough, add data to block and split if padding >=16 bytes
	{
		remove_free_list(bp);		
		
		/*Create header and footer with allocated size and set the allocation status to 1(allocated)*/
		PUT(HDRP(bp), PACK(asize, 1));	
 		PUT(FTRP(bp), PACK(asize, 1));
		
		nxt_bp = NEXT_BLKP(bp);
		
		/* Header and footer of the free (allocation status:0) block created after allocation*/
		PUT(HDRP(nxt_bp), PACK(csize-asize, 0));
 		PUT(FTRP(nxt_bp), PACK(csize-asize, 0));

		add_free_list(nxt_bp);

	}
		
	else					// Block created after extending heap, add data to block and a new free block couldnot fit in the remaining space
	{
		/*Create header and footer with allocated size and set the allocation status to 1(allocated)*/
		PUT(HDRP(bp), PACK(csize, 1));
 		PUT(FTRP(bp), PACK(csize, 1));

		remove_free_list(bp);
	}
	
}
static void remove_free_list(void *bp)
{
	int minlist; 
 	int size;
 	
 	gcount--; 
 	
 	size = GET_SIZE(HDRP(bp));		//get size of the block

 	
 	minlist = size / 50;			//calculate the minlist for the given block with a max of 83.
 	if(minlist > 83)
 		minlist = 83; 
 	
	if(GET(bp) == 0 && GET(bp + WSIZE) == 0) { 
 		PUT(heap_listp+(minlist * WSIZE), 0);
 		
 		if(gminlist == minlist) { 
 			if(gcount > 0){
 			int i;
 			for (i = minlist; GET(heap_listp+(i * WSIZE)) == 0; i++);
 			gminlist = i;
 			}
			else(gminlist = 100); 			
 		}
 	}
 	
 	else if (GET(bp) == 0 && GET(bp + WSIZE) != 0){
 		PUT(heap_listp+(minlist * WSIZE), GET(bp + WSIZE));
 		PUT((char *)GET(bp + WSIZE), 0);
 	}
 	
 	else if (GET(bp) != 0 && GET(bp + WSIZE) == 0) 
 		PUT(((char *)GET(bp) + WSIZE), 0);
 		
 	else {
 		PUT(((char *)GET(bp) + WSIZE), GET(bp + WSIZE));	
 		PUT(((char *)GET(bp + WSIZE)), GET(bp));	
 	}	
}

static void add_free_list(void *bp)
{
	int minlist;
 	void *temp_next;
 	void *temp_cur;
 	void *temp_prev;
 	int size;
 	
 	gcount++;			// Increment free count
 	
 	size = GET_SIZE(HDRP(bp));	// Get size of the block

 	
 	minlist = size / 50;
	if(minlist > 83)
		minlist = 83;
	
	if(gminlist > minlist || gminlist == 100)
		gminlist = minlist; //update global min list
	
	temp_cur = (char *)GET(heap_listp + (minlist * WSIZE));
	
	if(temp_cur == 0){
		PUT(heap_listp + (minlist * WSIZE), (int)bp);	
		PUT(bp, 0); 
		PUT(bp+WSIZE, 0);
	}
	
	else {
		temp_prev = (char *)GET(heap_listp + (minlist * WSIZE));
		
		for (; (int)temp_cur != 0 && GET_SIZE(HDRP(temp_cur)) < size; temp_cur = (char *)GET(temp_cur+WSIZE))
			temp_prev = temp_cur;
		
		temp_cur = temp_prev;
		
		temp_next = (char *)GET(temp_cur + WSIZE); 
		
		PUT(temp_cur + WSIZE, (int)bp); 

		if((int)temp_next != 0) 
			PUT(temp_next, (int)bp);
		
		PUT(bp, (int)temp_cur); 
		PUT(bp+WSIZE, (int)temp_next);
		
		}

}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
	void *oldptr = ptr;
	void *newptr;
	size_t oldsize;
	size_t asize = MAX(ALIGN(size) + DSIZE, 2*DSIZE);
    	
	oldsize = GET_SIZE(HDRP(oldptr));
	

	if(size == 0)			// If size is zero, it is equivalent to mm_free(ptr)
	{
		mm_free(ptr);
		newptr = 0;
		return NULL;
	}
	
	if(oldptr == NULL)		// If ptr is NULL, it is equivalent to mm_malloc(size)
	{
		return mm_malloc(size);	
	}
	
	
	
	if(asize == oldsize)		// If the size doesn't change, return original pointer
		return ptr;

	/* Block created after extending heap, add data to block and a new free block couldn't fit in the remaining space*/
	if(asize <= oldsize)
	{
		size = asize;

		if(oldsize - size <= 2*DSIZE)
			return ptr;
		
		PUT(HDRP(ptr), PACK(size, 1));
		PUT(FTRP(ptr), PACK(size, 1));
		PUT(HDRP(NEXT_BLKP(ptr)), PACK(oldsize-size, 1));
		mm_free(NEXT_BLKP(ptr));
		return ptr;
	}
	
	newptr = mm_malloc(size);
	
	/* If realloc() fails the original block is left untouched  */
	if(!newptr)
	{
		return 0;
	}

	
	if(size < oldsize) 		// Copy the old data
		oldsize = size;

	memcpy(newptr, ptr, oldsize);

	mm_free(ptr);			// Free the old block

	return newptr;

}

void mm_checkheap(int verbose)
{


}












