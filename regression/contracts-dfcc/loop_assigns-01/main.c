#include <assert.h>
#include <stdlib.h>

#define SIZE 8

struct blob
{
  char *data;
};

void main()
{
  foo();
}

void foo()
{
  struct blob *b = malloc(sizeof(struct blob));
  b->data = malloc(SIZE);
  struct blob *c;
  unsigned char *elem;
  unsigned char *k = malloc(5);
  struct blob d;
  char *data = malloc(100);
  d.data = malloc(100);

  b->data[5] = 0;
  for(unsigned i = 0; i < SIZE; i++)
    // clang-format off
    //__CPROVER_assigns(i, __CPROVER_object_whole(b->data),c, elem, __CPROVER_object_whole(elem))
    __CPROVER_loop_invariant(i <= SIZE)
    // clang-format on
    {
      elem = k;
      *elem = 1;
      b->data[i] = 1;
      d.data[i] = 1;
      data[i] = 1;
    }

  assert(b->data[5] == 0);
}
