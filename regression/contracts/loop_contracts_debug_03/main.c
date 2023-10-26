#define SIZE 80

void main()
{
  unsigned short len;
  __CPROVER_assume(len >= 8);
  char *array = malloc(len);
  const char *end = array + len;
  unsigned s = 0;

  while(array != end)
  __CPROVER_loop_invariant(__CPROVER_same_object(array, end) && __CPROVER_POINTER_OFFSET(array) <= __CPROVER_OBJECT_SIZE(array))
  {
    s += *array++;
  }
}
