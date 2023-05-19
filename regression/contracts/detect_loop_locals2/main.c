
const unsigned N =  65536;
inline int memcmp(const void *s1, const void *s2, unsigned n)
{
  int res=0;
  const unsigned char *sc1=s1, *sc2=s2;
  for(; n!=0; n--)
    __CPROVER_loop_invariant(n <= __CPROVER_loop_entry(n))
    __CPROVER_loop_invariant(__CPROVER_same_object(sc1, __CPROVER_loop_entry(sc1)))
    __CPROVER_loop_invariant(__CPROVER_same_object(sc2, __CPROVER_loop_entry(sc2)))
    __CPROVER_loop_invariant(sc1 <= s1 + __CPROVER_loop_entry(n))
    __CPROVER_loop_invariant(sc2 <= s2 + __CPROVER_loop_entry(n))
    __CPROVER_loop_invariant(res == 0)
    __CPROVER_loop_invariant(sc1 -(const unsigned char*)s1 == sc2 -(const unsigned char*)s2
     &&  sc1 -(const unsigned char*)s1== __CPROVER_loop_entry(n) - n)
  {     
    res = (*sc1++) - (*sc2++);
    long d1 = sc1 -(const unsigned char*)s1;
    long d2 = sc2 -(const unsigned char*)s2;
    if (res != 0)
      return res;
  }
  return res;
}

int main()
{
  unsigned SIZE;
  __CPROVER_assume(SIZE < 655360);
  unsigned char a[65535];
  unsigned char b[65535];
  assert(memcmp(a, b, 65535) == 0);
}
