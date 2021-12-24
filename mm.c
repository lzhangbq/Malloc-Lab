/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Liangwei Zhang <liangwez@andrew.cmu.edu>
 *
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

// Change:305,966

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = 2 * dsize;

/**
 * TODO: explain what chunksize is
 * It is the size of the initial free block and default size for expanding the
 * heap. (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: explain what alloc_mask is
 * Read the allocated bit from header by the least significant bit.
 */
static const word_t alloc_mask = 0x1;
static const word_t pre_alloc_mask = 0x2;
static const word_t pre_dsize_mask = 0x4;
/**
 * TODO: explain what size_mask is
 * Since the size is multiple of dsize due to alignment, the 4 least significant
 * bits must be 0 for the representation of size.
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.
     *
     * TODO: feel free to delete this comment once you've read it carefully.
     * We don't know what the size of the payload will be, so we will declare
     * it as a zero-length array, which is a GCC compiler extension. This will
     * allow us to obtain a pointer to the start of the payload.
     *
     * WARNING: A zero-length array must be the last element in a struct, so
     * there should not be any struct fields after it. For this lab, we will
     * allow you to include a zero-length array in a union, as long as the
     * union is the last field in its containing struct. However, this is
     * compiler-specific behavior and should be avoided in general.
     *
     * WARNING: DO NOT cast this pointer to/from other types! Instead, you
     * should use a union to alias this zero-length array with another struct,
     * in order to store additional types of data in the payload memory.
     */
    union {
        struct block *pointer;
        char payload[0];
    };

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Why can't we declare the block footer here as part of the struct?
     * Why do we even have footers -- will the code work fine without them?
     * which functions actually use the data contained in footers?
     *
     * The footer is the boundary tag which replicates the size and allocated
     * bit in the bottom. It is often used in coalescing for traversing
     * backwards. Declaring the footer may require extra space. Manipulating the
     * footer  may use extensive casting and pointer arithmetic.
     */
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;
static block_t *segregatehead[14]; // It is the start root pointer for seglists.
static bool last_block_dsize = false;   // We update the bool value for the last
                                        // block whether its size is dsize.
static bool last_block_prealloc = true; // We update the bool value for the last
                                        // block whether it is allocated.
/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    if (block == NULL) {
        return 0;
    }
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) >= min_block_size &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size >= min_block_size &&
               "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

// Since we make the min_block_size to 16, then we nned to construct a pointer
// to the previous free block in seglists.
static block_t *header_to_previous_pointer(block_t *block) {
    size_t size = get_size(block);
    dbg_assert(size > dsize && "Called footer_to_header on the prologue block");
    return (block_t *)(*(&block->pointer + 1));
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    if (block == NULL) {
        return 0;
    }
    return extract_alloc(block->header);
}

// Returns the allocation status for the previous block of a given header value.
static bool extract_pre_alloc(word_t word) {
    return (bool)(word & pre_alloc_mask);
}

// Returns the allocation status for the previous block of a block, based on its
// header.
static bool get_pre_alloc(block_t *block) {
    if (block == NULL) {
        return 0;
    }
    return extract_pre_alloc(block->header);
}

// Returns the dsize status for the previous block of a given header value.
static bool extract_dsize_mask(word_t word) {
    return (bool)(word & pre_dsize_mask);
}

// Returns the dsize status for the previous block of a block, based on its
// header.
static bool get_dsize_mask(block_t *block) {
    if (block == NULL) {
        return 0;
    }
    return extract_dsize_mask(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true);
}

// Check whether the footer is Heap prologue (block footer).
static bool is_epilogue_footer(word_t *footer) {
    if (extract_size(*footer) == 0 && extract_alloc(*footer) == true) {
        return true;
    }
    return false;
}

// Check whether the header is epilogue header.
static bool is_epilogue_header(block_t *block) {
    word_t header = block->header;
    if (extract_size(header) == 0 && extract_alloc(header) == true) {
        return true;
    }
    return false;
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 * @pre The block must be a valid block, not a boundary tag.
 * Important to notice the size of the block. If it is dsize, then we do not
 * write the footer.
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc);
    if (size >= min_block_size) {
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, alloc);
    }
}

// A new function to update the size and allocation status on header and/or
// footer, while remaining the value of pre_alloc and pre_dsize.
static void write_size_alloc(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    if (is_epilogue_header(block)) {
        return;
    }
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = block->header & 0xF;
    block->header |= size;
    if (alloc) {
        block->header |= alloc_mask;
    } else {
        word_t temp = ~(alloc_mask);
        block->header = block->header & temp;
    }
    if (size >= min_block_size) {
        word_t *footerp = header_to_footer(block);
        *footerp = block->header;
    }
}

// A new function to update the pre_allocation status on header and/or footer,
// while remaining the value of others.
static void write_pre_alloc(block_t *block, bool pre_alloc) {
    size_t size = get_size(block);
    if (is_epilogue_header(block)) {
        return;
    }
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    if (pre_alloc) {
        block->header |= pre_alloc_mask;
    } else {
        word_t temp = ~(pre_alloc_mask);
        block->header = block->header & temp;
    }
    if (size >= min_block_size && !get_alloc(block)) {
        word_t *footerp = header_to_footer(block);
        *footerp = block->header;
    }
}

// A new function to update the pre_dsize status on header and/or footer, while
// remaining the value of others.
static void write_pre_dsize(block_t *block, bool pre_dsize) {
    if (is_epilogue_header(block)) {
        return;
    }
    size_t size = get_size(block);
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    if (pre_dsize) {
        block->header |= pre_dsize_mask;
    } else {
        word_t temp = ~(pre_dsize_mask);
        block->header = block->header & temp;
    }
    if (size >= min_block_size && !get_alloc(block)) {
        word_t *footerp = header_to_footer(block);
        *footerp = block->header;
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    bool pre_dsize = get_dsize_mask(block);
    if (pre_dsize) {
        block_t *temp = (block_t *)((char *)block - dsize);
        return temp;
    } else {
        word_t *footerp = find_prev_footer(block);

        // Return NULL if called on first block in the heap
        if (extract_size(*footerp) == 0) {
            return NULL;
        }

        return footer_to_header(footerp);
    }
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @return
 */

// Find the corresponding index for seglist root for the size.
int findindex(size_t size) {
    if (size <= dsize) {
        return 0; // The block size is dsize.
    } else if (size <= 32) {
        return 1; // The block size is 32(min_block_size)
    } else if (size <= 64) {
        return 2; // The block size is 64(2 * min_block_size)
    } else if (size <= 96) {
        return 3; // The block size is 96(3 * min_block_size)
    } else if (size <= 128) {
        return 4; // The block size is 128(4 * min_block_size)
    } else if (size <= 256) {
        return 5; // The block size is [129,256]
    } else if (size <= 512) {
        return 6; // The block size is [257,512]
    } else if (size <= 1024) {
        return 7; // The block size is [513,1024]
    } else if (size <= 2048) {
        return 8; // The block size is [1025,2048]
    } else if (size <= 3072) {
        return 9; // The block size is [1025,2048]
    } else if (size <= 4096) {
        return 10; // The block size is [2049,4096]
    } else if (size <= 5120) {
        return 11; // The block size is [2049,4096]
    } else if (size <= 6144) {
        return 12; // The block size is [2049,4096]
    } else {
        return 13; // The block size is larger than 4096
    }
}

// Disconnect the block from the seglist.
static void disconnect(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    size_t block_size = get_size(block);
    int index = findindex(block_size);
    block_t *next = NULL;
    block_t *previous = NULL;
    if (index == 0 && block_size <= dsize) {
        if ((void *)(segregatehead[index]) == (void *)block) {
            next = block->pointer;
            segregatehead[index] = next;
            block->pointer = NULL;

        } else if (segregatehead[index] == NULL) {
            block->pointer = NULL;
        } else {
            block_t *temp = segregatehead[index];
            block_t *tempnext = NULL;
            while (temp != NULL) {
                if (temp->pointer == block) {
                    tempnext = block->pointer;
                    temp->pointer = tempnext;
                    block->pointer = NULL;
                    break;
                } else {
                    temp = temp->pointer;
                }
            }
        }
    } else {
        if ((void *)(segregatehead[index]) ==
            (void *)block) { // The block is the root.
            next = block->pointer;
            if (next) {
                segregatehead[index] = next;
                (*(&next->pointer + 1)) = NULL;
                block->pointer = NULL;
                (*(&block->pointer + 1)) = NULL;
            } else {
                segregatehead[index] = NULL;
                block->pointer = NULL;
                (*(&block->pointer + 1)) = NULL;
            }
        } else if (segregatehead[index] ==
                   NULL) { // Unusual cases found when debugging.
            block->pointer = NULL;
            (*(&block->pointer + 1)) = NULL;
        } else if (block->pointer == NULL && (*(&block->pointer + 1)) == NULL &&
                   (void *)block !=
                       (void
                            *)(segregatehead[index])) { // Sometimes it is
                                                        // already disconnected.
            return;
        } else if (block->pointer ==
                   NULL) { // It has the previous block but not the next block.
            previous = header_to_previous_pointer(block);
            previous->pointer = NULL;
            (*(&block->pointer + 1)) = NULL;
        } else if ((*(&block->pointer + 1)) ==
                   NULL) { // It has the next block but not the previous block.
            next = block->pointer;
            (*(&next->pointer + 1)) = NULL;
            segregatehead[index] = next;
            (*(&block->pointer + 1)) = NULL;
            block->pointer = NULL;
        } else { // It has the next block and the previous block.
            next = block->pointer;
            previous = header_to_previous_pointer(block);
            (*(&next->pointer + 1)) = previous;
            previous->pointer = next;
            block->pointer = NULL;
            (*(&block->pointer + 1)) = NULL;
        }
    }
}

// Link the block to the seglist. We adopt the LIFO policy.
static void link_to_the_list(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_alloc(block) == false);
    size_t size = get_size(block);
    int index = findindex(size);
    block_t *root = segregatehead[index];
    if (index == 0 && size <= dsize) {
        if (root == NULL) {
            segregatehead[index] = block;
            block->pointer = NULL;
        } else {
            block_t *temp = segregatehead[index];
            segregatehead[index] = block;
            block->pointer = temp;
        }
    } else {
        if (root == NULL) {
            segregatehead[index] = block;
            block->pointer = NULL;
            (*(&block->pointer + 1)) = NULL;
        } else {
            block_t *temp = segregatehead[index];
            if (size <= get_size(temp)) {
                segregatehead[index] = block;
                block->pointer = temp;
                (*(&block->pointer + 1)) = NULL;
                (*(&temp->pointer + 1)) = block;
            } else {
                segregatehead[index] = block;
                block->pointer = temp;
                (*(&block->pointer + 1)) = NULL;
                (*(&temp->pointer + 1)) = block;
            }
        }
    }
}

// Help function: Link the block and the previous one together.
static block_t *coalesce_previous(block_t *block) {
    size_t block_size = get_size(block);
    block_t *next = find_next(block);
    write_pre_dsize(next, false);
    if (is_epilogue_header(next)) {
        last_block_dsize = false;
    }
    if (get_dsize_mask(block)) {
        block_t *previousblock = (block_t *)((char *)block - dsize);
        size_t pre_size = get_size(previousblock);
        disconnect(previousblock);
        disconnect(block);
        block->header = 0;
        write_size_alloc(previousblock, pre_size + block_size, false);
        link_to_the_list(previousblock);
        return previousblock;
    } else {
        word_t *previousfooter = find_prev_footer(block);
        size_t pre_block_size = extract_size(*previousfooter);
        block_t *previous = find_prev(block);
        *previousfooter = 0;
        disconnect(previous);
        disconnect(block);
        block->header = 0;
        write_size_alloc(previous, pre_block_size + block_size, false);
        link_to_the_list(previous);
        return previous;
    }
}

// Help function: Link the block and the next one together.
static block_t *coalesce_next(block_t *block) {
    size_t block_size = get_size(block);
    block_t *next = find_next(block);
    size_t next_block_size = get_size(next);
    block_t *nextnext = find_next(next);
    if (is_epilogue_header(nextnext)) {
        last_block_dsize = false;
    }
    write_pre_dsize(nextnext, false);
    if (get_dsize_mask(next) || block_size < min_block_size) {
        disconnect(block);
        disconnect(next);
        next->header = 0;
        write_size_alloc(block, block_size + next_block_size, false);
        link_to_the_list(block);
        return block;
    } else {
        disconnect(block);
        disconnect(next);
        word_t *blockfooter = header_to_footer(block);
        *blockfooter = 0;
        next->header = 0;
        write_size_alloc(block, block_size + next_block_size, false);
        link_to_the_list(block);
        return block;
    }
}

// Help function: Link the block, the next one and the previous one together.
static block_t *coalesce_both(block_t *block) {
    size_t block_size = get_size(block);
    block_t *next = find_next(block);
    size_t next_block_size = get_size(next);
    block_t *nextnext = find_next(next);
    write_pre_dsize(nextnext, false);
    if (is_epilogue_header(nextnext)) {
        last_block_dsize = false;
    }
    if (get_dsize_mask(block)) {
        block_t *previousblock = (block_t *)((char *)block - dsize);
        size_t pre_size = get_size(previousblock);
        disconnect(previousblock);
        disconnect(block);
        disconnect(next);
        if (block_size >= min_block_size) {
            word_t *blockfooter = header_to_footer(block);
            *blockfooter = 0;
        }
        block->header = 0;
        next->header = 0;
        write_size_alloc(previousblock, pre_size + block_size + next_block_size,
                         false);
        link_to_the_list(previousblock);
        return previousblock;
    } else {
        word_t *previousfooter = find_prev_footer(block);
        size_t pre_block_size = extract_size(*previousfooter);
        block_t *previous = find_prev(block);
        *previousfooter = 0;
        disconnect(previous);
        disconnect(block);
        disconnect(next);
        if (block_size >= min_block_size) {
            word_t *blockfooter = header_to_footer(block);
            *blockfooter = 0;
        }
        block->header = 0;
        next->header = 0;
        write_size_alloc(previous,
                         pre_block_size + block_size + next_block_size, false);
        link_to_the_list(previous);
        return previous;
    }
}

static block_t *coalesce_block(block_t *block) {
    block_t *next = find_next(block);
    block_t *temp = NULL;
    if (get_pre_alloc(block) && (is_epilogue_header(next) || get_alloc(next))) {
        block->pointer = NULL;
        link_to_the_list(block);
        return block;
    } else if (get_pre_alloc(block)) {
        temp = coalesce_next(block);
        return temp;
    } else if (is_epilogue_header(next) || get_alloc(next)) {
        temp = coalesce_previous(block);
        return temp;
    } else {
        temp = coalesce_both(block);
        return temp;
    }
    return NULL;
}

/**
 * @brief
 *
 * <What does this function do?>
 * This function extends the heap if no space for new allocation.
 * <What are the function's arguments?>
 * The argument is the malloc size required.
 * <What is the function's return value?>
 * The function will return a new block address pointing to the new free block.
 * <Are there any preconditions or postconditions?>
 * The extend_heap should not be called many times, or mem_sbrk will fail.
 * The find_fit will return NULL before it is called.
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }
    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);
    if (block->pointer != NULL) {
        block->pointer = NULL;
    }
    if (size >= min_block_size) {
        (*(&block->pointer + 1)) = NULL;
    } // Sometimes the pointer address is not set to NULL. Should be done
      // manually to ensure the safety.

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_pre_alloc(block, last_block_prealloc);
    write_pre_dsize(block, last_block_dsize);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * Sometimes the malloc size is less than the original size. We should split it
 * and relink the new size freeblock to the seglists for further use. <What are
 * the function's arguments?> The arguments are the block address where it will
 * be allocated. asize is the requried allocation size. <What is the function's
 * return value?> It will return void. But we will allocate the block and
 * construct the new remaining free block if possible, then we will relink it to
 * the seglists. <Are there any preconditions or postconditions?> The block
 * should be allocated. We check whether the remaining size can be constructed
 * as a new block. If the remaining size is dsize, then we should construct it
 * into different ways.
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    /*TODO: Can you write a precondition about the value of asize? */
    // The asize must be the multiple of 16 Bytes.

    size_t block_size = get_size(block);
    block_t *next = find_next(block);
    word_t *footerblock;
    if ((block_size - asize) < dsize) {
        if (is_epilogue_header(next)) {
            last_block_prealloc = true;
            if (asize == dsize && block_size < min_block_size) {
                last_block_dsize = true;
            } else {
                last_block_dsize = false;
            }
        } else {
            write_pre_alloc(next, true);
        }
        if (asize >= min_block_size) {
            footerblock = header_to_footer(block);
            *footerblock = 0;
        }
    } else if ((block_size - asize) < min_block_size) {
        block_t *block_next;
        write_size_alloc(block, asize, true);
        block_next = find_next(block);
        write_block(block_next, block_size - asize, false);
        if (asize <= dsize) {
            write_pre_dsize(block_next, true);
            block->pointer = NULL;
        }
        write_pre_alloc(block_next, true);
        write_pre_alloc(next, false);
        write_pre_dsize(next, true);
        if (is_epilogue_header(next)) {
            last_block_prealloc = false;
            last_block_dsize = true;
        }
        if (asize >= min_block_size) {
            footerblock = header_to_footer(block);
            *footerblock = 0;
        }
        link_to_the_list(block_next);
    } else {
        block_t *block_next;
        write_size_alloc(block, asize, true);
        block_next = find_next(block);
        write_block(block_next, block_size - asize, false);
        if (asize <= dsize) {
            write_pre_dsize(block_next, true);
        }
        write_pre_alloc(block_next, true);
        if (is_epilogue_header(next)) {
            last_block_prealloc = false;
            last_block_dsize = false;
        }
        if (asize >= min_block_size) {
            footerblock = header_to_footer(block);
            *footerblock = 0;
        }
        link_to_the_list(block_next);
    }
    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * <What does this function do?>
 * This function find the suitable free block for allocation.
 * <What are the function's arguments?>
 * The argument is asize, which is the required allocated block size.
 * <What is the function's return value?>
 * It will return the block address found. If not found, it will return NULL.
 * <Are there any preconditions or postconditions?>
 * We iterate the index of segregatehead and must ensure that index must not go
 * out of range.
 *
 * @param[in] asize
 * @return
 */
// FIrst fit policy.
static block_t *find_fit(size_t asize) {
    block_t *block = NULL;
    block_t *temp = NULL;
    block_t *blocknext = NULL;
    int index = findindex(asize);
    bool finish = true; // It stops when we find a good list.
    while (finish) {
        temp = segregatehead[index];
        if (temp == NULL) {
            index++;
            if (index == 14) {
                return NULL;
                break;
            } // If no find, we search for a list with larger size. Stops when
              // all lists are not valid.
        } else {
            block = temp;
            blocknext = block->pointer;
            while (block != NULL) {
                if (get_size(block) >= asize && !(get_alloc(block))) {
                    finish = false;
                    size_t difference = get_size(block) - asize;
                    if (difference > 0) {
                        int i = 0;
                        block_t *findtemp = block->pointer;
                        block_t *result = block;
                        while (i < 10 && findtemp != NULL) {
                            i++;
                            size_t tempdiffer = difference;
                            if (get_size(findtemp) >= asize) {
                                tempdiffer = get_size(findtemp) - asize;
                                if (tempdiffer == 0) {
                                    return findtemp;
                                    break;
                                } else if (tempdiffer < difference) {
                                    result = findtemp;
                                    difference = tempdiffer;
                                }
                            }
                            findtemp = findtemp->pointer;
                        } // Better fit. For the first fit block, find the
                          // better suitable blocks in the next 10 blocks.
                        return result;
                    } else {
                        return block;
                    }
                } else {
                    block = blocknext;
                    if (block != NULL) {
                        blocknext = block->pointer;
                    }
                } // Find the first fit on the seglist.
            }
            index++;
            if (index == 14) {
                return NULL;
                break;
            }
        }
    }

    return NULL;
}

// Helper function: Test the validity of each block.
bool check_block_valid(block_t *block) {
    if (is_epilogue_header(block) || block == NULL) {
        return true;
    } else if (get_size(block) == dsize) {
        size_t blocksize = get_size(block);
        size_t payloadsize = get_payload_size(block);
        if (payloadsize != wsize || blocksize % dsize != 0 ||
            blocksize != dsize) {
            return false;
        }
    } else {
        word_t header = block->header;
        word_t *footer = header_to_footer(block);
        if ((extract_size(header) != extract_size(*footer)) ||
            (extract_alloc(header) != extract_alloc(*footer))) {
            return false;
        }
        size_t blocksize = get_size(block);
        size_t payloadsize = get_payload_size(block);
        if (payloadsize % dsize != 0 || blocksize % dsize != 0 ||
            blocksize < min_block_size ||
            payloadsize < (min_block_size - dsize)) {
            return false;
        }
    }
    return true;
}

// Helper function: Test the validity of each seglist line.
bool check_line(block_t *root, int index) {
    block_t *testblock = NULL;
    block_t *testblocknext = NULL;
    int testindex = 0;
    size_t blocksize;
    if (index == 0) {
        testblock = root;
        while (root != NULL) {
            if (!check_block_valid(testblock)) {
                return false;
            }
            if (extract_alloc(testblock->header)) {
                return false;
            }
            blocksize = get_size(testblock);
            testindex = findindex(blocksize);
            if (testindex != index) {
                return false;
            }
            testblocknext = testblock->pointer;
            testblock = testblocknext;
        }
        return true;
    } else {
        if (root != NULL) {
            testblock = root;
            while (testblock != NULL) {
                if (!check_block_valid(testblock)) {
                    return false;
                }
                if (extract_alloc(testblock->header) ||
                    extract_alloc(*(header_to_footer(testblock)))) {
                    return false;
                }
                blocksize = get_size(testblock);
                testindex = findindex(blocksize);
                if (testindex != index) {
                    return false;
                }
                testblocknext = testblock->pointer;

                if (testblocknext != NULL) {
                    if (*(&testblocknext->pointer + 1) != testblock) {
                        return false;
                    }
                }

                testblock = testblocknext;
            }
        }
        return true;
    }
}

/**
 * @brief
 *
 * <What does this function do?>
 * This function acts as the debug funtion to check the correctness of the heap.
 * <What are the function's arguments?>
 * It put in the heap line number.
 * <What is the function's return value?>
 * It will return bool value for whether the heap is correct.
 * <Are there any preconditions or postconditions?>
 * Take notice of the epilogue header and prologue footer. Check the correctness
 * for each block and each seglist.
 *
 * @param[in] line
 * @return
 */
bool mm_checkheap(int line) {
    word_t *epilogue_footer = find_prev_footer(heap_start);
    block_t *testblock = NULL;
    block_t *testlineroot = NULL;
    if (!is_epilogue_footer(
            epilogue_footer)) { // Check the previous footer of heap start is
                                // prologue footer.
        return false;
    }
    if (!is_epilogue_header(
            heap_start)) { // The case when it is already working (The heap
                           // start is not epilogue header).
        testblock = heap_start;
        while (!is_epilogue_header(testblock) && testblock != NULL) {
            if (!check_block_valid(testblock)) {
                return false;
            }
            testblock = find_next(testblock);
        } // Traverse through the whole heap and check the validity of each
          // block.
        for (int i = 0; i < 4; i++) {
            testlineroot = segregatehead[i];
            if (!check_line(testlineroot, i)) {
                return false;
            } // Test each seglist.
        }
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * This function initializes the heap.
 * <What are the function's arguments?>
 * Void input.
 * <What is the function's return value?>
 * It will return an initialized free heap with chunksize.
 * <Are there any preconditions or postconditions?>
 * No.
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));
    if (start == (void *)-1) {
        return false;
    }
    for (int i = 0; i < 14; i++) {
        segregatehead[i] = NULL;
    }
    start[0] = pack(0, true); // Heap prologue (block footer)
    start[1] = pack(
        0,
        true); // Heap epilogue (block header)
               // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);
    last_block_prealloc = true;
    block_t *extendheap = extend_heap(chunksize);
    // Extend the empty heap with a free block of bytes
    if (extendheap == NULL) {
        return false;
    }
    int index = findindex(get_size(extendheap));
    segregatehead[index] = extendheap;
    extendheap->pointer = NULL;
    (*(&extendheap->pointer + 1)) = NULL;
    write_pre_alloc(extendheap, true);
    last_block_prealloc = false;
    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * It allocates a space with size.
 * <What are the function's arguments?>
 * It inputs the allocated size.
 * <What is the function's return value?>
 * It will return the payload address for the allocated space.
 * <Are there any preconditions or postconditions?>
 * It must work after the initialization of the heap.
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);

    write_size_alloc(block, block_size, true);
    disconnect(block);
    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * It frees a allocated space.
 * <What are the function's arguments?>
 * It inputs the payload address.
 * <What is the function's return value?>
 * It will return void.
 * <Are there any preconditions or postconditions?>
 * bp should not bu NULL. After freeing, we should coalesce the possible free
 blocks. payload_to_header
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_size_alloc(block, size, false);
    block->pointer = NULL;
    if (size >= min_block_size) {
        (*(&block->pointer + 1)) = NULL;
    }
    block_t *block_next = find_next(block);
    write_pre_alloc(block_next, false);
    if (is_epilogue_header(block_next)) {
        last_block_prealloc = false;
    }

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * It reallocate the space.
 * <What are the function's arguments?>
 * It inputs the payload address and new allocation size.
 * <What is the function's return value?>
 * It will return void.
 * <Are there any preconditions or postconditions?>
 * It returns NULL for invalid size and becomes malloc if payload address is
 * NULL.
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * Allocates memory for an array of elements of size bytes each.
 * <What are the function's arguments?>
 * It inputs the number of elements and the size for each element.
 * <What is the function's return value?>
 * It returns a pointer to the allocated memory.
 * <Are there any preconditions or postconditions?>
 * The number of elelments is larger than 0 and the allocated size should be the
 * multiple of number and size.
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
