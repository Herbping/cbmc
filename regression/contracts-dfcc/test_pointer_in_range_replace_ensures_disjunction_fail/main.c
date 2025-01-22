
typedef struct
{
  int *a;
  int *x;
} ret_t;

ret_t foo()
  // clang-format off
  __CPROVER_ensures(__CPROVER_is_fresh(__CPROVER_return_value.a, 8*sizeof(int)))
  __CPROVER_ensures(
    __CPROVER_pointer_in_range_dfcc(
      __CPROVER_return_value.a,
      __CPROVER_return_value.x,
      __CPROVER_return_value.a + 7
    ) || 1)
  // clang-format on
  ;

void bar()
{
  ret_t ret = foo();
  int *x = ret.x;
  *x = 0; //expected to fail
}

void main()
{
  bar();
}
