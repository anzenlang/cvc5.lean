import cvc5Test.Init

/-! # Black box testing of the term manager

- <https://github.com/cvc5/cvc5/blob/e342ecb325520619db2a1f49e95f96ebca8029f2/test/unit/api/cpp/api_term_manager_black.cpp>
-/
namespace cvc5.Test

test![TestApiBlackTermManager, getBooleanSort] tm => do
  tm.getBooleanSort |> assertOkDiscard

test![TestApiBlackTermManager, getIntegerSort] tm => do
  tm.getIntegerSort |> assertOkDiscard

test![TestApiBlackTermManager, getRealSort] tm => do
  tm.getRealSort |> assertOkDiscard

test![TestApiBlackTermManager, getRegExpSort] tm => do
  tm.getRegExpSort |> assertOkDiscard

test![TestApiBlackTermManager, getStringSort] tm => do
  tm.getStringSort |> assertOkDiscard

test![TestApiBlackTermManager, getRoundingModeSort] tm => do
  tm.getRoundingModeSort |> assertOkDiscard

test![TestApiBlackTermManager, mkArraySort] tm => do
  let boolSort ← tm.getBooleanSort
  let intSort ← tm.getIntegerSort
  let realSort ← tm.getRealSort
  let bvSort ← tm.mkBitVectorSort 32

  let size ← bvSort.getBitVectorSize |> assertOk
  assertEq size 32

  tm.mkArraySort boolSort boolSort |> assertOkDiscard
  tm.mkArraySort intSort intSort |> assertOkDiscard
  tm.mkArraySort realSort realSort |> assertOkDiscard
  tm.mkArraySort bvSort bvSort |> assertOkDiscard
  tm.mkArraySort boolSort intSort |> assertOkDiscard
  tm.mkArraySort realSort bvSort |> assertOkDiscard

  let fpSort ← tm.mkFloatingPointSort 3 5
  tm.mkArraySort fpSort fpSort |> assertOkDiscard
  tm.mkArraySort bvSort fpSort |> assertOkDiscard
  tm.mkArraySort boolSort boolSort |> assertOkDiscard

  tm.mkArraySort (← tm.getBooleanSort) (← tm.getIntegerSort) |> assertOkDiscard

test![TestApiBlackTermManager, mkBitVectorSort] tm => do
  tm.mkBitVectorSort 32 |> assertOkDiscard
  tm.mkBitVectorSort 0 |> assertError "invalid argument '0' for 'size', expected size > 0"

test![TestApiBlackTermManager, mkFiniteFieldSort] tm => do
  tm.mkFiniteFieldSort 31 |> assertOkDiscard
  tm.mkFiniteFieldSort 6 |> assertError
    "invalid argument '6' for 'modulus', expected modulus is prime"

  tm.mkFiniteFieldSort 1100101 2 |> assertOkDiscard
  tm.mkFiniteFieldSort 10202 3 |> assertOkDiscard
  tm.mkFiniteFieldSort 401 5 |> assertOkDiscard
  tm.mkFiniteFieldSortOfString "791a" 11 |> assertOkDiscard
  tm.mkFiniteFieldSortOfString "970f" 16 |> assertOkDiscard
  tm.mkFiniteFieldSortOfString "8CC5" 16 |> assertOkDiscard

  tm.mkFiniteFieldSort 1100100 2 |> assertError
    "invalid argument '1100100' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 10201 3 |> assertError
    "invalid argument '10201' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 400 5 |> assertError
    "invalid argument '400' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 7919 11 |> assertError
    "invalid argument '7919' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSortOfString "970e" 16 |> assertError
    "invalid argument '970e' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSortOfString "8CC4" 16 |> assertError
    "invalid argument '8CC4' for 'modulus', expected modulus is prime"

test![TestApiBlackTermManager, mkFloatingPointSort] tm => do
  tm.mkFloatingPointSort 4 8 |> assertOkDiscard

  tm.mkFloatingPointSort 0 8 |> assertError
    "invalid argument '0' for 'exp', expected exponent size > 1"
  tm.mkFloatingPointSort 4 0 |> assertError
    "invalid argument '0' for 'sig', expected significand size > 1"
  tm.mkFloatingPointSort 1 8 |> assertError
    "invalid argument '1' for 'exp', expected exponent size > 1"
  tm.mkFloatingPointSort 4 1 |> assertError
    "invalid argument '1' for 'sig', expected significand size > 1"

test![TestApiBlackTermManager, mkDatatypeSort] tm => do
  let int ← tm.getIntegerSort

  let _scope ← do
    let mut dtSpec ← tm.mkDatatypeDecl "list"
    let mut consSpec ← tm.mkDatatypeConstructorDecl "cons"
    consSpec ← consSpec.addSelector "head" int
    dtSpec ← dtSpec.addConstructor consSpec
    let nilSpec ← tm.mkDatatypeConstructorDecl "nil"
    dtSpec ← dtSpec.addConstructor nilSpec
    tm.mkDatatypeSort dtSpec |> assertOkDiscard

    tm.mkDatatypeSort dtSpec |> assertError
      "Given datatype declaration is already resolved \
      (has already been used to create a datatype sort)"
    tm.mkDatatypeSort dtSpec |> assertError
      "Given datatype declaration is already resolved \
      (has already been used to create a datatype sort)"

  let badDtSpec ← tm.mkDatatypeDecl "list"
  tm.mkDatatypeSort badDtSpec |> assertError
    "invalid argument 'DATATYPE list = \n END;\n' for 'dtypedecl', \
    expected a datatype declaration with at least one constructor"

  let _scope ← do
    let tm' ← TermManager.new
    let mut dtSpec' ← tm'.mkDatatypeDecl "list"
    let mut consSpec' ← tm'.mkDatatypeConstructorDecl "cons"
    consSpec' ← consSpec'.addSelector "head" (← tm'.getIntegerSort)
    dtSpec' ← dtSpec'.addConstructor consSpec'
    let nilSpec' ← tm'.mkDatatypeConstructorDecl "nil"
    dtSpec' ← dtSpec'.addConstructor nilSpec'
    tm.mkDatatypeSort dtSpec' |> assertError
      "Given datatype declaration is not associated with this term manager"

test![TestApiBlackTermManager, mkDatatypeSorts] tm => do
  let int ← tm.getIntegerSort
  let bool ← tm.getBooleanSort

  let _scope ← do
    let mut dt1Spec ← tm.mkDatatypeDecl "list1"
    let mut cons1Spec ← tm.mkDatatypeConstructorDecl "cons1"
    cons1Spec ← cons1Spec.addSelector "head1" int
    dt1Spec ← dt1Spec.addConstructor cons1Spec
    let nil1Spec ← tm.mkDatatypeConstructorDecl "nil1"
    dt1Spec ← dt1Spec.addConstructor nil1Spec
    let mut dt2Spec ← tm.mkDatatypeDecl "list2"
    let mut cons2Spec ← tm.mkDatatypeConstructorDecl "cons2"
    cons2Spec ← cons2Spec.addSelector "head2" int
    dt2Spec ← dt2Spec.addConstructor cons2Spec
    let nil2Spec ← tm.mkDatatypeConstructorDecl "nil2"
    dt2Spec ← dt2Spec.addConstructor nil2Spec
    let decls := #[dt1Spec, dt2Spec]
    tm.mkDatatypeSorts decls |> assertOkDiscard

    tm.mkDatatypeSorts decls |> assertError
      "Given datatype declaration is already resolved \
      (has already been used to create a datatype sort)"
    tm.mkDatatypeSorts decls |> assertError
      "Given datatype declaration is already resolved \
      (has already been used to create a datatype sort)"

  let badDtSpec ← tm.mkDatatypeDecl "list"
  let badDecls := #[badDtSpec]
  tm.mkDatatypeSorts badDecls |> assertError
    "invalid datatype declaration in 'dtypedecls' at index 0, \
    expected a datatype declaration with at least one constructor"

  -- with unresolved sorts
  let unresList ← tm.mkUnresolvedDatatypeSort "ulist"
  let mut ulist ← tm.mkDatatypeDecl "ulist"
  let mut uconsSpec ← tm.mkDatatypeConstructorDecl "ucons"
  uconsSpec ← uconsSpec.addSelector "car" unresList
  uconsSpec ← uconsSpec.addSelector "cdr" unresList
  ulist ← ulist.addConstructor uconsSpec
  let unilSpec ← tm.mkDatatypeConstructorDecl "unil"
  ulist ← ulist.addConstructor unilSpec
  let udecls := #[ulist]
  tm.mkDatatypeSorts udecls |> assertOkDiscard

  tm.mkDatatypeSorts udecls |> assertError
    "Given datatype declaration is already resolved \
    (has already been used to create a datatype sort)"
  tm.mkDatatypeSorts udecls |> assertError
    "Given datatype declaration is already resolved \
    (has already been used to create a datatype sort)"

  -- mutually recursive with unresolved parameterized sorts
  let p0 ← tm.mkParamSort "p0"
  let p1 ← tm.mkParamSort "p1"
  let u0 ← tm.mkUnresolvedDatatypeSort "dt0" 1
  let u1 ← tm.mkUnresolvedDatatypeSort "dt1" 1
  let mut dt0Spec ← tm.mkDatatypeDecl "dt0" #[p0]
  let mut dt1Spec ← tm.mkDatatypeDecl "dt1" #[p1]
  let mut ctor0Spec ← tm.mkDatatypeConstructorDecl "c0"
  ctor0Spec ← ctor0Spec.addSelector "s0" (← u1.instantiate #[p0])
  let mut ctor1Spec ← tm.mkDatatypeConstructorDecl "c1"
  ctor1Spec ← ctor1Spec.addSelector "s1" (← u0.instantiate #[p1])
  dt0Spec ← dt0Spec.addConstructor ctor0Spec
  dt1Spec ← dt1Spec.addConstructor ctor1Spec
  dt1Spec ← dt1Spec.addConstructor (← tm.mkDatatypeConstructorDecl "nil")
  let dtSorts ← tm.mkDatatypeSorts #[dt0Spec, dt1Spec]
  let isort1 ← dtSorts[1]!.instantiate #[bool]
  let t1 ← tm.mkConst isort1 "t"
  let t0 ← do
    let selector ← DatatypeSelector.getTerm (← t1.getSort.getDatatype!.getSelector "s1")
    tm.mkTerm Kind.APPLY_SELECTOR #[selector, t1]
  assertEq t0.getSort (dtSorts[0]!.instantiate! #[bool])

  let _scope ← do
    let tm' ← TermManager.new
    let int' ← tm'.getIntegerSort
    let mut dt1Spec' ← tm'.mkDatatypeDecl "list1"
    let mut cons1Spec' ← tm'.mkDatatypeConstructorDecl "cons1"
    cons1Spec' ← cons1Spec'.addSelector "head1" int'
    dt1Spec' ← dt1Spec'.addConstructor cons1Spec'
    let nil1Spec' ← tm'.mkDatatypeConstructorDecl "nil1"
    dt1Spec' ← dt1Spec'.addConstructor nil1Spec'
    let mut dt2Spec' ← tm'.mkDatatypeDecl "list2"
    let mut cons2Spec' ← tm'.mkDatatypeConstructorDecl "cons2"
    cons2Spec' ← cons2Spec'.addSelector "head2" int'
    dt2Spec' ← dt2Spec'.addConstructor cons2Spec'
    let nil2Spec ← tm'.mkDatatypeConstructorDecl "nil2"
    dt2Spec' ← dt2Spec'.addConstructor nil2Spec
    let decls' := #[dt1Spec', dt2Spec']
    tm.mkDatatypeSorts decls' |> assertError
      "invalid datatype declaration in 'dtypedecls' at index 0, \
      expected a datatype declaration associated with this term manager"


test![TestApiBlackTermManager, mkFunctionSort] tm => do
  let uf ← tm.mkUninterpretedSort "u" |> assertOk
  let int ← tm.getIntegerSort
  let funSort ← tm.mkFunctionSort #[uf] int |> assertOk

  -- function arguments are allowed
  tm.mkFunctionSort #[funSort] int |> assertOkDiscard
  -- non-first-class arguments are not allowed
  tm.mkFunctionSort #[int] funSort |> assertError
    "invalid argument '(-> u Int)' for 'codomain', expected non-function sort as codomain sort"
  --
  tm.mkFunctionSort #[uf, int] int |> assertOkDiscard

  let funSort2 ← tm.mkFunctionSort #[← tm.mkUninterpretedSort "u"] (← tm.getBooleanSort) |> assertOk
  --
  tm.mkFunctionSort #[funSort2, uf] int |> assertOkDiscard
  --
  tm.mkFunctionSort #[int, uf] funSort2 |> assertError
    "invalid argument '(-> u Bool)' for 'codomain', expected non-function sort as codomain sort"

  let bool ← tm.getBooleanSort
  let sorts1 := #[bool, int, int]
  let sorts2 := #[bool, int]

  tm.mkFunctionSort sorts2 int |> assertOkDiscard
  tm.mkFunctionSort sorts1 int |> assertOkDiscard

  let tm' ← TermManager.new
  let bool' ← tm'.getBooleanSort
  let int' ← tm'.getIntegerSort
  tm'.mkFunctionSort sorts2 int' |> assertError
    "invalid domain sort in 'sorts' at index 0, expected a sort associated with this term manager"
  tm'.mkFunctionSort #[bool', int'] int |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkParamSort] tm => do
  tm.mkParamSort "T" |> assertOkDiscard
  tm.mkParamSort "" |> assertOkDiscard

test![TestApiBlackTermManager, mkPredicateSort] tm => do
  tm.mkPredicateSort #[← tm.getIntegerSort] |> assertOkDiscard
  tm.mkPredicateSort #[] |> assertError
    "invalid size of argument 'sorts', expected at least one parameter sort for predicate sort"
  -- function as arguments are allowed
  let funSort ← tm.mkFunctionSort #[← tm.mkUninterpretedSort "u"] (← tm.getIntegerSort)
  tm.mkPredicateSort #[← tm.getIntegerSort, funSort] |> assertOkDiscard
  tm.mkPredicateSort #[← tm.getIntegerSort] |> assertOkDiscard

  let tm' ← TermManager.new
  tm'.mkPredicateSort #[← tm.getIntegerSort] |> assertError
    "invalid domain sort in 'sorts' at index 0, expected a sort associated with this term manager"

test![TestApiBlackTermManager, mkRecordSort] tm => do
  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort
  let bv ← tm.mkBitVectorSort 8
  let fields := #[ ("b", bool), ("bv", bv), ("i", int) ]
  let empty := #[]
  tm.mkRecordSort fields |> assertOkDiscard
  tm.mkRecordSort empty |> assertOkDiscard
  let recSort ← tm.mkRecordSort fields
  recSort.getDatatype |> assertOkDiscard
  tm.mkRecordSort fields |> assertOkDiscard

  let tm' ← TermManager.new
  tm'.mkRecordSort
    #[ ("b", ← tm'.getBooleanSort), ("bv", ← tm.mkBitVectorSort 8), ("b", ← tm'.getIntegerSort) ]
  |> assertError
    "invalid sort in 'fields' at index 1, expected a sort associated with this term manager"

test![TestApiBlackTermManager, mkSetSort] tm => do
  tm.getBooleanSort >>= tm.mkSetSort |> assertOkDiscard
  tm.getIntegerSort >>= tm.mkSetSort |> assertOkDiscard
  tm.mkBitVectorSort 4 >>= tm.mkSetSort |> assertOkDiscard
  tm.mkBitVectorSort 4 >>= tm.mkSetSort |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.getBooleanSort >>= tm.mkSetSort |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkBagSort] tm => do
  tm.getBooleanSort >>= tm.mkBagSort |> assertOkDiscard
  tm.getIntegerSort >>= tm.mkBagSort |> assertOkDiscard
  tm.mkBitVectorSort 4 >>= tm.mkBagSort |> assertOkDiscard
  tm.mkBitVectorSort 4 >>= tm.mkBagSort |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.getBooleanSort >>= tm.mkBagSort |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkSequenceSort] tm => do
  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort
  tm.mkSequenceSort bool |> assertOkDiscard
  tm.mkSequenceSort int >>= tm.mkSequenceSort |> assertOkDiscard
  tm.mkSequenceSort int |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.getBooleanSort >>= tm.mkSequenceSort |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkAbstractSort] tm => do
  tm.mkAbstractSort SortKind.ARRAY_SORT |> assertOkDiscard
  tm.mkAbstractSort SortKind.BITVECTOR_SORT |> assertOkDiscard
  tm.mkAbstractSort SortKind.TUPLE_SORT |> assertOkDiscard
  tm.mkAbstractSort SortKind.SET_SORT |> assertOkDiscard
  tm.mkAbstractSort SortKind.BOOLEAN_SORT |> assertError
    "cannot construct abstract type for kind BOOLEAN_SORT"

test![TestApiBlackTermManager, mkUninterpretedSort] tm => do
  tm.mkUninterpretedSort "u" |> assertOkDiscard
  tm.mkUninterpretedSort "" |> assertOkDiscard

test![TestApiBlackTermManager, mkUnresolvedDatatypeSort] tm => do
  tm.mkUnresolvedDatatypeSort "u" |> assertOkDiscard
  tm.mkUnresolvedDatatypeSort "u" 1 |> assertOkDiscard
  tm.mkUnresolvedDatatypeSort "" |> assertOkDiscard
  tm.mkUnresolvedDatatypeSort "" 1 |> assertOkDiscard

test![TestApiBlackTermManager, mkUninterpretedSortConstructorSort] tm => do
  tm.mkUninterpretedSortConstructorSort 2 "s" |> assertOkDiscard
  tm.mkUninterpretedSortConstructorSort 2 "" |> assertOkDiscard
  tm.mkUninterpretedSortConstructorSort 0 |> assertError
    "invalid argument '0' for 'arity', expected an arity > 0"

test![TestApiBlackTermManager, mkTupleSort] tm => do
  let int ← tm.getIntegerSort
  tm.mkTupleSort #[int] |> assertOkDiscard
  let funSort ← tm.mkFunctionSort #[ ← tm.mkUninterpretedSort "u"] int
  tm.mkTupleSort #[int, funSort] |> assertOkDiscard
  tm.mkTupleSort #[int] |> assertOkDiscard
  let tm' ← TermManager.new
  tm.mkTupleSort #[← tm'.getBooleanSort] |> assertError
    "invalid domain sort in 'sorts' at index 0, expected a sort associated with this term manager"

test![TestApiBlackTermManager, mkNullableSort] tm => do
  tm.getIntegerSort >>= tm.mkNullableSort |> assertOkDiscard
  tm.getIntegerSort >>= tm.mkNullableSort |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.getIntegerSort >>= tm.mkNullableSort |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkBitVector] tm => do
  tm.mkBitVector 8 2 |> assertOkDiscard
  tm.mkBitVector 32 2 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "-1111111" 2 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "0101" 2 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "00000101" 2 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "-127" 10 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "255" 10 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "-7f" 16 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "a0" 16 |> assertOkDiscard

  tm.mkBitVector 0 2 |> assertError
    "invalid argument '0' for 'size', expected a bit-width > 0"
  tm.mkBitVectorOfString 0 "-127" 10 |> assertError
    "invalid argument '0' for 'size', expected a bit-width > 0"
  tm.mkBitVectorOfString 0 "a0" 16 |> assertError
    "invalid argument '0' for 'size', expected a bit-width > 0"

  tm.mkBitVectorOfString 8 "" 2 |> assertError
    "invalid argument '' for 's', expected a non-empty string"

  tm.mkBitVectorOfString 8 "101" 5 |> assertError
    "invalid argument '5' for 'base', expected base 2, 10, or 16"
  tm.mkBitVectorOfString 8 "128" 11 |> assertError
    "invalid argument '11' for 'base', expected base 2, 10, or 16"
  tm.mkBitVectorOfString 8 "a0" 21 |> assertError
    "invalid argument '21' for 'base', expected base 2, 10, or 16"

  tm.mkBitVectorOfString 8 "-11111111" 2 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value -11111111)"
  tm.mkBitVectorOfString 8 "101010101" 2 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value 101010101)"
  tm.mkBitVectorOfString 8 "-256" 10 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value -256)"
  tm.mkBitVectorOfString 8 "257" 10 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value 257)"
  tm.mkBitVectorOfString 8 "-a0" 16 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value -a0)"
  tm.mkBitVectorOfString 8 "fffff" 16 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value fffff)"

  tm.mkBitVectorOfString 8 "10201010" 2 |> assertError "mpz_set_str"
  tm.mkBitVectorOfString 8 "-25x" 10 |> assertError "mpz_set_str"
  tm.mkBitVectorOfString 8 "2x7" 10 |> assertError "mpz_set_str"
  tm.mkBitVectorOfString 8 "fzff" 16 |> assertError "mpz_set_str"

  assertEq (← tm.mkBitVectorOfString 8 "0101" 2) (← tm.mkBitVectorOfString 8 "00000101" 2)
  assertEq (← tm.mkBitVectorOfString 4 "-1" 2) (← tm.mkBitVectorOfString 4 "1111" 2)
  assertEq (← tm.mkBitVectorOfString 4 "-1" 16) (← tm.mkBitVectorOfString 4 "1111" 2)
  assertEq (← tm.mkBitVectorOfString 4 "-1" 10) (← tm.mkBitVectorOfString 4 "1111" 2)
  assertEq "#b01010101" (← tm.mkBitVectorOfString 8 "01010101" 2).toString
  assertEq "#b00001111" (← tm.mkBitVectorOfString 8 "F" 16).toString
  assertEq (← tm.mkBitVectorOfString 8 "-1" 10) (← tm.mkBitVectorOfString 8 "FF" 16)

test![TestApiBlackTermManager, mkFiniteFieldElem] tm => do
  let f ← tm.mkFiniteFieldSort 7
  let bv ← tm.mkBitVectorSort 4

  tm.mkFiniteFieldElem "0" f |> assertOkDiscard
  tm.mkFiniteFieldElem "1" f |> assertOkDiscard
  tm.mkFiniteFieldElem "6" f |> assertOkDiscard
  tm.mkFiniteFieldElem "8" f |> assertOkDiscard
  tm.mkFiniteFieldElem "-1" f |> assertOkDiscard

  tm.mkFiniteFieldElem "a" f |> assertError "mpz_set_str"

  tm.mkFiniteFieldElem "-1" bv |> assertError
    "invalid argument '(_ BitVec 4)' for 'sort', expected a finite field sort"

  assertEq (← tm.mkFiniteFieldElem "-1" f) (← tm.mkFiniteFieldElem "6" f)
  assertEq (← tm.mkFiniteFieldElem "1" f) (← tm.mkFiniteFieldElem "8" f)

  tm.mkFiniteFieldElem "0" f 2 |> assertOkDiscard
  tm.mkFiniteFieldElem "101" f 3 |> assertOkDiscard
  tm.mkFiniteFieldElem "-10" f 7 |> assertOkDiscard
  tm.mkFiniteFieldElem "abcde" f 16 |> assertOkDiscard

  assertEq (← tm.mkFiniteFieldElem "0" f 2) (← tm.mkFiniteFieldElem "0" f 3)
  assertEq (← tm.mkFiniteFieldElem "11" f 2) (← tm.mkFiniteFieldElem "10" f 3)
  assertEq (← tm.mkFiniteFieldElem "1010" f 2) (← tm.mkFiniteFieldElem "A" f 16)

  assertEq (← tm.mkFiniteFieldElem "-22" f 3) (← tm.mkFiniteFieldElem "10" f 6)

test![TestApiBlackTermManager, mkConstArray] tm => do
  let intSort ← tm.getIntegerSort
  let arrSort ← tm.mkArraySort intSort intSort
  let zero ← tm.mkInteger 0
  let _constArr ← tm.mkConstArray arrSort zero -- unused in original test

  tm.mkConstArray (cvc5.Sort.null ()) zero |> assertError
    "invalid null argument for 'sort'"
  tm.mkConstArray arrSort (Term.null ()) |> assertError
    "invalid null argument for 'val'"
  tm.mkConstArray arrSort (← tm.mkBitVector 1 1) |> assertError
    "value does not match element sort"

  let zero2 ← tm.mkInteger 0
  let arrSort2 ← tm.mkArraySort (← tm.getIntegerSort) (← tm.getIntegerSort)
  tm.mkConstArray arrSort2 zero |> assertOkDiscard
  tm.mkConstArray arrSort zero2 |> assertOkDiscard
  let tm' ← TermManager.new
  let int' ← tm'.getIntegerSort
  tm'.mkConstArray arrSort (← tm'.mkInteger 0) |> assertError
    "Given sort is not associated with this term manager"
  tm'.mkConstArray (← tm'.mkArraySort int' int') zero |> assertError
    "Given term is not associated with this term manager"

test![TestApiBlackTermManager, mkVar] tm => do
  let boolSort ← tm.getBooleanSort
  let intSort ← tm.getIntegerSort
  let funSort ← tm.mkFunctionSort #[intSort] boolSort
  tm.mkVar boolSort |> assertOkDiscard
  tm.mkVar funSort |> assertOkDiscard
  tm.mkVar boolSort "b" |> assertOkDiscard
  tm.mkVar funSort "" |> assertOkDiscard
  tm.mkVar (Sort.null ()) |> assertError "invalid null argument for 'sort'"
  tm.mkVar (Sort.null ()) "a" |> assertError "invalid null argument for 'sort'"
  tm.mkVar boolSort "x" |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.mkVar boolSort "c" |> assertError "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkBoolean] tm => do
  tm.mkBoolean true |> assertOkDiscard
  tm.mkBoolean false |> assertOkDiscard

test![TestApiBlackTermManager, mkRoundingMode] tm => do
  assertEq "roundNearestTiesToEven"
    (← tm.mkRoundingMode RoundingMode.ROUND_NEAREST_TIES_TO_EVEN).toString
  assertEq "roundTowardPositive"
    (← tm.mkRoundingMode RoundingMode.ROUND_TOWARD_POSITIVE).toString
  assertEq "roundTowardNegative"
    (← tm.mkRoundingMode RoundingMode.ROUND_TOWARD_NEGATIVE).toString
  assertEq "roundTowardZero"
    (← tm.mkRoundingMode RoundingMode.ROUND_TOWARD_ZERO).toString
  assertEq "roundNearestTiesToAway"
    (← tm.mkRoundingMode RoundingMode.ROUND_NEAREST_TIES_TO_AWAY).toString

test![TestApiBlackTermManager, mkRoundingMode] tm => do
  let t1 ← tm.mkBitVector 8
  let t2 ← tm.mkBitVector 4
  tm.mkFloatingPoint 3 5 t1 |> assertOkDiscard
  tm.mkFloatingPoint 0 5 (Term.null ()) |> assertError "invalid null argument for 'val'"
  tm.mkFloatingPoint 0 5 t1 |> assertError
    "invalid argument '0' for 'exp', expected exponent size > 1"
  tm.mkFloatingPoint 1 5 t1 |> assertError
    "invalid argument '1' for 'exp', expected exponent size > 1"
  tm.mkFloatingPoint 3 0 t1 |> assertError
    "invalid argument '0' for 'sig', expected significand size > 1"
  tm.mkFloatingPoint 3 1 t1 |> assertError
    "invalid argument '1' for 'sig', expected significand size > 1"
  tm.mkFloatingPoint 3 3 t2 |> assertError
    "invalid argument '#b0000' for 'val', expected a bit-vector value with bit-width '6'"

  assertEq
    (← tm.mkFloatingPointOfComponents
      (← tm.mkBitVector 1) (← tm.mkBitVector 5) (← tm.mkBitVector 10))
    (← tm.mkFloatingPoint 5 11 (← tm.mkBitVector 16))
  tm.mkFloatingPointOfComponents (Term.null ()) (← tm.mkBitVector 5) (← tm.mkBitVector 10)
  |> assertError "invalid null argument for 'sign'"
  tm.mkFloatingPointOfComponents (← tm.mkBitVector 1) (Term.null ()) (← tm.mkBitVector 10)
  |> assertError "invalid null argument for 'exp'"
  tm.mkFloatingPointOfComponents (← tm.mkBitVector 1) (← tm.mkBitVector 5) (Term.null ())
  |> assertError "invalid null argument for 'sig'"
  tm.mkFloatingPointOfComponents
    (← tm.mkConst (← tm.mkBitVectorSort 1)) (← tm.mkBitVector 5) (← tm.mkBitVector 10)
  |> assertError "invalid argument '||' for 'sign', expected bit-vector value"
  tm.mkFloatingPointOfComponents
    (← tm.mkBitVector 1) (← tm.mkConst (← tm.mkBitVectorSort 5)) (← tm.mkBitVector 10)
  |> assertError "invalid argument '||' for 'exp', expected bit-vector value"
  tm.mkFloatingPointOfComponents
    (← tm.mkBitVector 1) (← tm.mkBitVector 5) (← tm.mkConst (← tm.mkBitVectorSort 5))
  |> assertError "invalid argument '||' for 'sig', expected bit-vector value"
  tm.mkFloatingPointOfComponents
    (← tm.mkBitVector 2) (← tm.mkBitVector 5) (← tm.mkBitVector 10)
  |> assertError "invalid argument '#b00' for 'sign', expected a bit-vector value of size 1"

  let tm' ← TermManager.new
  tm'.mkFloatingPoint 3 5 t1 |> assertError
    "Given term is not associated with this term manager"
  tm'.mkFloatingPointOfComponents (← tm.mkBitVector 1) (← tm'.mkBitVector 5) (← tm'.mkBitVector 10)
  |> assertError "Given term is not associated with this term manager"
  tm'.mkFloatingPointOfComponents (← tm'.mkBitVector 1) (← tm.mkBitVector 5) (← tm'.mkBitVector 10)
  |> assertError "Given term is not associated with this term manager"
  tm'.mkFloatingPointOfComponents (← tm'.mkBitVector 1) (← tm'.mkBitVector 5) (← tm.mkBitVector 10)
  |> assertError "Given term is not associated with this term manager"

test![TestApiBlackTermManager, mkCardinalityConstraint] tm => do
  let su ← tm.mkUninterpretedSort "u"
  let si ← tm.getIntegerSort
  tm.mkCardinalityConstraint su 3 |> assertOkDiscard
  tm.mkCardinalityConstraint si 3 |> assertError
    "invalid argument 'Int' for 'sort', expected an uninterpreted sort"
  tm.mkCardinalityConstraint su 0 |> assertError
    "invalid argument '0' for 'upperBound', expected a value > 0"
  tm.mkCardinalityConstraint su 3 |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.mkCardinalityConstraint su 3 |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkEmptyBag] tm => do
  let s ← tm.mkSetSort (← tm.getBooleanSort)
  tm.mkEmptySet (Sort.null ()) |> assertError
    "invalid null argument for 'sort'"
  tm.mkEmptySet s |> assertOkDiscard
  tm.mkEmptySet (← tm.getBooleanSort) |> assertError
    "invalid argument 'Bool' for 'sort', expected null sort or set sort"
  tm.mkEmptySet s |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.mkEmptySet s |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkEmptyBag] tm => do
  let s ← tm.mkBagSort (← tm.getBooleanSort)
  tm.mkEmptyBag (Sort.null ()) |> assertError
    "invalid null argument for 'sort'"
  tm.mkEmptyBag s |> assertOkDiscard
  tm.mkEmptyBag (← tm.getBooleanSort) |> assertError
    "invalid argument 'Bool' for 'sort', expected null sort or bag sort"
  tm.mkEmptyBag s |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.mkEmptyBag s |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkEmptySequence] tm => do
  let s ← tm.mkSequenceSort (← tm.getBooleanSort)
  tm.mkEmptySequence s |> assertOkDiscard
  tm.mkEmptySequence (← tm.getBooleanSort) |> assertOkDiscard
  tm.mkEmptySequence s |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.mkEmptySequence s |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkFalse] tm => do
  tm.mkFalse |> assertOkDiscard
  tm.mkFalse |> assertOkDiscard

test![TestApiBlackTermManager, mkFloatingPointNaN] tm => do
  tm.mkFloatingPointNaN 3 5 |> assertOkDiscard

test![TestApiBlackTermManager, mkFloatingPointNegZero] tm => do
  tm.mkFloatingPointNegZero 3 5 |> assertOkDiscard

test![TestApiBlackTermManager, mkFloatingPointNegInf] tm => do
  tm.mkFloatingPointNegInf 3 5 |> assertOkDiscard

test![TestApiBlackTermManager, mkFloatingPointPosInf] tm => do
  tm.mkFloatingPointPosInf 3 5 |> assertOkDiscard

test![TestApiBlackTermManager, mkFloatingPointPosZero] tm => do
  tm.mkFloatingPointPosZero 3 5 |> assertOkDiscard
  tm.mkFloatingPointPosZero 3 5 |> assertOkDiscard

test![TestApiBlackTermManager, mkOp] tm => do
  -- mkOpOfString
  tm.mkOpOfString Kind.DIVISIBLE "2147483648" |> assertOkDiscard
  tm.mkOpOfString Kind.BITVECTOR_EXTRACT "asdf" |> assertError
    "invalid kind 'BITVECTOR_EXTRACT', expected DIVISIBLE"

  -- mkOp
  tm.mkOp Kind.DIVISIBLE #[1] |> assertOkDiscard
  tm.mkOp Kind.BITVECTOR_ROTATE_LEFT #[1] |> assertOkDiscard
  tm.mkOp Kind.BITVECTOR_ROTATE_RIGHT #[1] |> assertOkDiscard
  tm.mkOp Kind.BITVECTOR_EXTRACT #[1] |> assertError
    "invalid number of indices for operator BITVECTOR_EXTRACT, expected 2 but got 1."

  tm.mkOp Kind.BITVECTOR_EXTRACT #[1, 1] |> assertOkDiscard
  tm.mkOp Kind.DIVISIBLE #[1, 2] |> assertError
    "invalid number of indices for operator DIVISIBLE, expected 1 but got 2."

  tm.mkOp Kind.TUPLE_PROJECT #[1, 2, 2] |> assertOkDiscard

test![TestApiBlackTermManager, mkPi] tm => do
  tm.mkPi |> assertOkDiscard

test![TestApiBlackTermManager, mkInteger] tm => do
  tm.mkIntegerOfString "123" |> assertOkDiscard
  tm.mkIntegerOfString "1.23" |> assertError
    "invalid argument '1.23' for 's', expected an integer "
  tm.mkIntegerOfString "1/23" |> assertError
    "invalid argument '1/23' for 's', expected an integer "
  tm.mkIntegerOfString "12/3" |> assertError
    "invalid argument '12/3' for 's', expected an integer "
  tm.mkIntegerOfString ".2" |> assertError "invalid argument '.2' for 's', expected an integer "
  tm.mkIntegerOfString "2." |> assertError "invalid argument '2.' for 's', expected an integer "
  tm.mkIntegerOfString "" |> assertError "invalid argument '' for 's', expected an integer "
  tm.mkIntegerOfString "asdf" |> assertError
    "invalid argument 'asdf' for 's', expected an integer "
  tm.mkIntegerOfString "1.2/3" |> assertError
    "invalid argument '1.2/3' for 's', expected an integer "
  tm.mkIntegerOfString "." |> assertError "invalid argument '.' for 's', expected an integer "
  tm.mkIntegerOfString "/" |> assertError "invalid argument '/' for 's', expected an integer "
  tm.mkIntegerOfString "2/" |> assertError "invalid argument '2/' for 's', expected an integer "
  tm.mkIntegerOfString "/2" |> assertError "invalid argument '/2' for 's', expected an integer "

  tm.mkInteger 1 |> assertOkDiscard
  tm.mkInteger (- 1) |> assertOkDiscard
  -- not in the original test
  tm.mkInteger 0 |> assertOkDiscard
  tm.mkInteger (- 123456789101112131415) |> assertOkDiscard
  tm.mkInteger 123456789101112131415 |> assertOkDiscard

test![TestApiBlackTermManager, mkReal] tm => do
  tm.mkRealOfString "123" |> assertOkDiscard
  tm.mkRealOfString "1.23" |> assertOkDiscard
  tm.mkRealOfString "1/23" |> assertOkDiscard
  tm.mkRealOfString "12/3" |> assertOkDiscard
  tm.mkRealOfString ".2" |> assertOkDiscard
  tm.mkRealOfString "2." |> assertOkDiscard
  tm.mkRealOfString "" |> assertError "cannot construct Real or Int from string argument ''"
  tm.mkRealOfString "asdf" |> assertError
    "cannot construct Real or Int from string argument 'asdf'"
  tm.mkRealOfString "1.2/3" |> assertError
    "cannot construct Real or Int from string argument '1.2/3'"
  tm.mkRealOfString "." |> assertError
    "invalid argument '.' for 's', expected a string representing a real or rational value."
  tm.mkRealOfString "/" |> assertError "cannot construct Real or Int from string argument '/'"
  tm.mkRealOfString "2/" |> assertError "cannot construct Real or Int from string argument '2/'"
  tm.mkRealOfString "/2" |> assertError "cannot construct Real or Int from string argument '/2'"

  -- the original test has more values to test different (u)int encodings, but we only accept `Int`
  -- numerical values
  let val1 : Int := 1
  let val2 := - 1
  tm.mkReal val1 |> assertOkDiscard
  tm.mkReal val2 |> assertOkDiscard
  tm.mkReal val2 |> assertOkDiscard
  tm.mkReal val1 val1 |> assertOkDiscard
  tm.mkReal val2 val2 |> assertOkDiscard
  tm.mkRealOfString "-1/-1" |> assertOkDiscard
  tm.mkRealOfString "1/-1" |> assertOkDiscard
  tm.mkRealOfString "-1/1" |> assertOkDiscard
  tm.mkRealOfString "1/1" |> assertOkDiscard
  tm.mkRealOfString "/-5" |> assertError "cannot construct Real or Int from string argument '/-5'"
  -- the original test checks that division by zero (`Int`) fails, but we ask for a proof that this
  -- can't happen
  tm.mkRealOfString "1/0" |> assertError "cannot construct Real or Int from string argument '1/0'"

  -- not in the original test
  tm.mkRealOfRat (mkRat val1 1) |> assertOkDiscard

test![TestApiBlackTermManager, mkRegexpAll] tm => do
  let strSort ← tm.getStringSort
  let s ← tm.mkConst strSort "s"
  tm.mkTerm Kind.STRING_IN_REGEXP #[s, ← tm.mkRegexpAll] |> assertOkDiscard

test![TestApiBlackTermManager, mkRegexpAllchar] tm => do
  let strSort ← tm.getStringSort
  let s ← tm.mkConst strSort "s"
  tm.mkTerm Kind.STRING_IN_REGEXP #[s, ← tm.mkRegexpAllchar] |> assertOkDiscard

test![TestApiBlackTermManager, mkRegexpNone] tm => do
  let strSort ← tm.getStringSort
  let s ← tm.mkConst strSort "s"
  tm.mkTerm Kind.STRING_IN_REGEXP #[s, ← tm.mkRegexpNone] |> assertOkDiscard

test![TestApiBlackTermManager, mkSepEmp] tm => do
  tm.mkSepEmp |> assertOkDiscard

test![TestApiBlackTermManager, mkSepNil] tm => do
  tm.mkSepNil (← tm.getBooleanSort) |> assertOkDiscard
  tm.mkSepNil (Sort.null ()) |> assertError "invalid null argument for 'sort'"
  tm.mkSepNil (← tm.getIntegerSort) |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.mkSepNil (← tm.getBooleanSort) |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkString] tm => do
  tm.mkString "" |> assertOkDiscard
  tm.mkString "asdfasdf" |> assertOkDiscard
  assertEq "\"asdf\\u{5c}nasdf\"" (← tm.mkString "asdf\\nasdf").toString
  assertEq "\"asdf\\u{5c}nasdf\"" (← tm.mkString "asdf\u005cnasdf").toString

  let strings := ["", "ascii text", "utf8 → π ←"]
  for s in strings do
    assertEq (← (← tm.mkString s).getStringValue) s

test![TestApiBlackTermManager, mkTerm] tm => do
  let bv32Sort ← tm.mkBitVectorSort 32
  let a ← tm.mkConst bv32Sort "a"
  let b ← tm.mkConst bv32Sort "b"
  let v1 := #[a, b]
  let v2 := #[a, Term.null ()]
  let v3 := #[a, ← tm.mkTrue]
  let _v4 := #[← tm.mkInteger 1, ← tm.mkInteger 2]
  let _v5 := #[← tm.mkInteger 1, Term.null ()]
  let v6 := #[]

  tm.mkTerm Kind.PI |> assertOkDiscard
  tm.mkTerm Kind.PI v6 |> assertOkDiscard
  tm.mkTermOfOp (← tm.mkOp Kind.PI) |> assertOkDiscard
  tm.mkTermOfOp (← tm.mkOp Kind.PI) v6 |> assertOkDiscard
  tm.mkTerm Kind.REGEXP_NONE |> assertOkDiscard
  tm.mkTerm Kind.REGEXP_NONE v6 |> assertOkDiscard
  tm.mkTermOfOp (← tm.mkOp Kind.REGEXP_NONE) |> assertOkDiscard
  tm.mkTermOfOp (← tm.mkOp Kind.REGEXP_NONE) v6 |> assertOkDiscard
  tm.mkTerm Kind.REGEXP_ALLCHAR |> assertOkDiscard
  tm.mkTerm Kind.REGEXP_ALLCHAR v6 |> assertOkDiscard
  tm.mkTermOfOp (← tm.mkOp Kind.REGEXP_ALLCHAR) |> assertOkDiscard
  tm.mkTermOfOp (← tm.mkOp Kind.REGEXP_ALLCHAR) v6 |> assertOkDiscard
  tm.mkTerm Kind.SEP_EMP |> assertOkDiscard
  tm.mkTerm Kind.SEP_EMP v6 |> assertOkDiscard
  tm.mkTermOfOp (← tm.mkOp Kind.SEP_EMP) |> assertOkDiscard
  tm.mkTermOfOp (← tm.mkOp Kind.SEP_EMP) v6 |> assertOkDiscard
  tm.mkTerm Kind.CONST_BITVECTOR |> assertError
    "invalid kind 'CONST_BITVECTOR', \
    expected PI, REGEXP_NONE, REGEXP_ALL, REGEXP_ALLCHAR or SEP_EMP"

  tm.mkTerm Kind.NOT #[← tm.mkTrue] |> assertOkDiscard
  tm.mkTerm Kind.BAG_MAKE #[← tm.mkTrue, ← tm.mkInteger 1] |> assertOkDiscard
  tm.mkTerm Kind.NOT #[Term.null ()] |> assertError
    "invalid null term in 'children' at index 0"
  tm.mkTerm Kind.NOT #[a] |> assertError "expecting a Boolean subexpression"
  tm.mkTerm Kind.NOT #[← tm.mkTrue] |> assertOkDiscard

  tm.mkTerm Kind.EQUAL #[a, b] |> assertOkDiscard
  tm.mkTerm Kind.EQUAL #[Term.null (), b] |> assertError
    "invalid null term in 'children' at index 0"
  tm.mkTerm Kind.EQUAL #[a, Term.null ()] |> assertError
    "invalid null term in 'children' at index 1"
  tm.mkTerm Kind.EQUAL #[a, ← tm.mkTrue] |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= a true)\nType 1: (_ BitVec 32)\nType 2: Bool"
  tm.mkTerm Kind.EQUAL #[a, b] |> assertOkDiscard

  tm.mkTerm Kind.ITE #[← tm.mkTrue, ← tm.mkTrue, ← tm.mkTrue] |> assertOkDiscard
  tm.mkTerm Kind.ITE #[Term.null (), ← tm.mkTrue, ← tm.mkTrue] |> assertError
    "invalid null term in 'children' at index 0"
  tm.mkTerm Kind.ITE #[← tm.mkTrue, Term.null (), ← tm.mkTrue] |> assertError
    "invalid null term in 'children' at index 1"
  tm.mkTerm Kind.ITE #[← tm.mkTrue, ← tm.mkTrue, Term.null ()] |> assertError
    "invalid null term in 'children' at index 2"
  tm.mkTerm Kind.ITE #[← tm.mkTrue, ← tm.mkTrue, b] |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: true\nits type   : Bool\nelse branch: b\nits type   : (_ BitVec 32)"
  tm.mkTerm Kind.ITE #[← tm.mkTrue, ← tm.mkTrue, ← tm.mkTrue] |> assertOkDiscard

  tm.mkTerm Kind.EQUAL v1 |> assertOkDiscard
  tm.mkTerm Kind.EQUAL v2 |> assertError "invalid null term in 'children' at index 1"
  tm.mkTerm Kind.EQUAL v3 |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= a true)\nType 1: (_ BitVec 32)\nType 2: Bool"
  tm.mkTerm Kind.DISTINCT v6 |> assertError
    "invalid kind 'DISTINCT', expected PI, REGEXP_NONE, REGEXP_ALL, REGEXP_ALLCHAR or SEP_EMP"

  -- test cases that are nary via the API but but have arity = 2 internally
  let _scope ← do
    let sBool ← tm.getBooleanSort
    let tBool ← tm.mkConst sBool "tBool"
    tm.mkTerm Kind.IMPLIES #[tBool, tBool, tBool] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.IMPLIES) #[tBool, tBool, tBool] |> assertOkDiscard
    tm.mkTerm Kind.XOR #[tBool, tBool, tBool] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.XOR) #[tBool, tBool, tBool] |> assertOkDiscard
    let tInt ← tm.mkConst (← tm.getIntegerSort) "tInt"
    tm.mkTerm Kind.DIVISION #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.DIVISION) #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTerm Kind.INTS_DIVISION #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.INTS_DIVISION) #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTerm Kind.SUB #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.SUB) #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTerm Kind.EQUAL #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.EQUAL) #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTerm Kind.LT #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.LT) #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTerm Kind.GT #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.GT) #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTerm Kind.LEQ #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.LEQ) #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTerm Kind.GEQ #[tInt, tInt, tInt] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.GEQ) #[tInt, tInt, tInt] |> assertOkDiscard
    let tReg ← tm.mkConst (← tm.getRegExpSort) "tReg"
    tm.mkTerm Kind.REGEXP_DIFF #[tReg, tReg, tReg] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.REGEXP_DIFF) #[tReg, tReg, tReg] |> assertOkDiscard
    let tFun ← tm.mkConst (← tm.mkFunctionSort #[sBool, sBool, sBool] sBool)
    tm.mkTerm Kind.HO_APPLY #[tFun, tBool, tBool, tBool] |> assertOkDiscard
    tm.mkTermOfOp (← tm.mkOp Kind.HO_APPLY) #[tFun, tBool, tBool, tBool] |> assertOkDiscard

  let tm' ← TermManager.new
  tm.mkTerm Kind.ITE #[← tm.mkTrue, ← tm'.mkTrue, ← tm'.mkTrue] |> assertError
    "invalid term in 'children' at index 1, expected a term associated with this term manager"
  tm.mkTerm Kind.ITE #[← tm'.mkTrue, ← tm.mkTrue, ← tm'.mkTrue] |> assertError
    "invalid term in 'children' at index 0, expected a term associated with this term manager"
  tm.mkTerm Kind.ITE #[← tm'.mkTrue, ← tm'.mkTrue, ← tm.mkTrue] |> assertError
    "invalid term in 'children' at index 0, expected a term associated with this term manager"

test![TestApiBlackTermManager, mkTermOfOp] tm => do
  let bv32Sort ← tm.mkBitVectorSort 32
  let a ← tm.mkConst bv32Sort "a"
  let b ← tm.mkConst bv32Sort "b"
  let v1 := #[← tm.mkInteger 1, ← tm.mkInteger 2]
  let v2 := #[← tm.mkInteger 1, Term.null ()]
  let v3 := #[]
  let v4 := #[← tm.mkInteger 5]

  -- simple operator terms
  let opTerm1 ← tm.mkOp Kind.BITVECTOR_EXTRACT #[2, 1]
  let opTerm2 ← tm.mkOp Kind.DIVISIBLE #[1]

  -- list datatype
  let sort ← tm.mkParamSort "T"
  let mut listSpec ← tm.mkDatatypeDecl "paramList" #[sort]
  let mut consSpec ← tm.mkDatatypeConstructorDecl "cons"
  let nilSpec ← tm.mkDatatypeConstructorDecl "nil"
  consSpec ← consSpec.addSelector "head" sort
  consSpec ← consSpec.addSelectorSelf "tail"
  listSpec ← listSpec.addConstructor consSpec
  listSpec ← listSpec.addConstructor nilSpec
  let listSort ← tm.mkDatatypeSort listSpec
  let intListSort ← listSort.instantiate #[← tm.getIntegerSort]
  let c ← tm.mkConst intListSort "c"
  let list ← listSort.getDatatype

  -- list datatype constructor and selector operator terms
  let consTerm ← (← list.getConstructor "cons").getTerm
  let nilTerm ← (← list.getConstructor "nil").getTerm
  let headTerm ← (← list[0]!.getSelector "head").getTerm
  let tailTerm ← list[0]![1]!.getTerm

  let _scope ← do
    tm.mkTerm Kind.APPLY_CONSTRUCTOR #[nilTerm] |> assertOkDiscard
    tm.mkTerm Kind.APPLY_SELECTOR #[nilTerm] |> assertError
      "invalid kind 'APPLY_SELECTOR', \
      expected Terms with kind APPLY_SELECTOR must have at least 2 children and at most 2 children \
      (the one under construction has 1)"
    tm.mkTerm Kind.APPLY_SELECTOR #[consTerm] |> assertError
      "invalid kind 'APPLY_SELECTOR', \
      expected Terms with kind APPLY_SELECTOR must have at least 2 children \
      and at most 2 children (the one under construction has 1)"
    tm.mkTerm Kind.APPLY_CONSTRUCTOR #[consTerm] |> assertError
      "number of arguments does not match the constructor type"
    tm.mkTermOfOp opTerm1 |> assertError
      "invalid kind 'BITVECTOR_EXTRACT', \
      expected Terms with kind BITVECTOR_EXTRACT must have at least 1 children \
      and at most 1 children (the one under construction has 0)"
    tm.mkTerm Kind.APPLY_SELECTOR #[headTerm] |> assertError
      "invalid kind 'APPLY_SELECTOR', \
      expected Terms with kind APPLY_SELECTOR must have at least 2 children \
      and at most 2 children (the one under construction has 1)"
    tm.mkTermOfOp opTerm1 |> assertError
      "invalid kind 'BITVECTOR_EXTRACT', \
      expected Terms with kind BITVECTOR_EXTRACT must have at least 1 children \
      and at most 1 children (the one under construction has 0)"
    tm.mkTerm Kind.APPLY_CONSTRUCTOR #[nilTerm] |> assertOkDiscard

  let _scope ← do
    tm.mkTermOfOp opTerm1 #[a] |> assertOkDiscard
    tm.mkTermOfOp opTerm2 #[← tm.mkInteger 1] |> assertOkDiscard
    tm.mkTerm Kind.APPLY_SELECTOR #[headTerm, c] |> assertOkDiscard
    tm.mkTerm Kind.APPLY_SELECTOR #[tailTerm, c] |> assertOkDiscard
    tm.mkTermOfOp opTerm2 #[a] |> assertError
      "Expecting a integer term as the first argument in 'divisible'"
    tm.mkTermOfOp opTerm1 #[Term.null ()] |> assertError
      "invalid null term in 'children' at index 0"
    tm.mkTerm Kind.APPLY_CONSTRUCTOR #[consTerm, ← tm.mkInteger 0] |> assertError
      "number of arguments does not match the constructor type"
    tm.mkTermOfOp opTerm1 #[a] |> assertOkDiscard

  let _scope ← do
    tm.mkTerm Kind.APPLY_CONSTRUCTOR
      #[consTerm, ← tm.mkInteger 0, ← tm.mkTerm Kind.APPLY_CONSTRUCTOR #[nilTerm]]
    |> assertOkDiscard
    tm.mkTermOfOp opTerm2 #[← tm.mkInteger 1, ← tm.mkInteger 2] |> assertError
      "invalid kind 'DIVISIBLE', \
      expected Terms with kind DIVISIBLE must have at least 1 children \
      and at most 1 children (the one under construction has 2)"
    tm.mkTermOfOp opTerm1 #[a, b] |> assertError
      "invalid kind 'BITVECTOR_EXTRACT', \
      expected Terms with kind BITVECTOR_EXTRACT must have at least 1 children \
      and at most 1 children (the one under construction has 2)"
    tm.mkTermOfOp opTerm2 #[← tm.mkInteger 1, Term.null ()] |> assertError
      "invalid null term in 'children' at index 1"
    tm.mkTermOfOp opTerm2 #[Term.null (), ← tm.mkInteger 1] |> assertError
      "invalid null term in 'children' at index 0"
    tm.mkTerm Kind.APPLY_CONSTRUCTOR
      #[consTerm, ← tm.mkInteger 0, ← tm.mkTerm Kind.APPLY_CONSTRUCTOR #[nilTerm]]
    |> assertOkDiscard

  tm.mkTermOfOp opTerm1 #[a, b, a] |> assertError
    "invalid kind 'BITVECTOR_EXTRACT', \
    expected Terms with kind BITVECTOR_EXTRACT must have at least 1 children \
    and at most 1 children (the one under construction has 3)"
  tm.mkTermOfOp opTerm2 #[← tm.mkInteger 1, ← tm.mkInteger 1, Term.null ()] |> assertError
    "invalid null term in 'children' at index 2"

  tm.mkTermOfOp opTerm2 v4 |> assertOkDiscard
  tm.mkTermOfOp opTerm2 v1 |> assertError
    "invalid kind 'DIVISIBLE', \
    expected Terms with kind DIVISIBLE must have at least 1 children \
    and at most 1 children (the one under construction has 2)"
  tm.mkTermOfOp opTerm2 v2 |> assertError "invalid null term in 'children' at index 1"
  tm.mkTermOfOp opTerm2 v3 |> assertError
    "invalid kind 'DIVISIBLE', \
    expected Terms with kind DIVISIBLE must have at least 1 children \
    and at most 1 children (the one under construction has 0)"
  tm.mkTermOfOp opTerm2 v4 |> assertOkDiscard

test![TestApiBlackTermManager, mkTrue] tm => do
  tm.mkTrue |> assertOkDiscard
  tm.mkTrue |> assertOkDiscard

test![TestApiBlackTermManager, mkTuple] tm => do
  tm.mkTuple #[← tm.mkBitVectorOfString 3 "101" 2] |> assertOkDiscard
  tm.mkTuple #[← tm.mkInteger 5] |> assertOkDiscard
  tm.mkTuple #[← tm.mkRealOfString "5.3"] |> assertOkDiscard
  tm.mkTuple #[← tm.mkBitVectorOfString 3 "101" 2] |> assertOkDiscard
  tm.mkTuple #[← tm.mkBitVectorOfString 3 "101" 2] |> assertOkDiscard

  let tm' ← TermManager.new
  tm'.mkTuple #[← tm.mkBitVectorOfString 3 "101" 2] |> assertError
    "invalid term in 'terms' at index 0, expected a term associated with this term manager"

test![TestApiBlackTermManager, mkNullableSome] tm => do
  tm.mkNullableSome (← tm.mkBitVectorOfString 3 "101" 2) |> assertOkDiscard
  tm.mkNullableSome (← tm.mkInteger 5) |> assertOkDiscard
  tm.mkNullableSome (← tm.mkRealOfString "5.3") |> assertOkDiscard
  tm.mkNullableSome (← tm.mkBitVectorOfString 3 "101" 2) |> assertOkDiscard
  tm.mkNullableSome (← tm.mkBitVectorOfString 3 "101" 2) |> assertOkDiscard

  let tm' ← TermManager.new
  tm'.mkNullableSome (← tm.mkBitVectorOfString 3 "101" 2) |> assertError
    "Given term is not associated with this term manager"

test![TestApiBlackTermManager, mkNullableVal] tm => do
  let mut value ← tm.mkNullableVal (← tm.mkNullableSome (← tm.mkInteger 5))
  let solver ← Solver.new tm
  value ← solver.simplify value
  assertEq 5 value.getIntegerValue!

  let tm' ← TermManager.new
  tm'.mkNullableVal (← tm.mkNullableSome (← tm.mkBitVectorOfString 3 "101" 2)) |> assertError
    "Given term is not associated with this term manager"

test![TestApiBlackTermManager, mkNullableIsNull] tm => do
  let mut value ← tm.mkNullableIsNull (← tm.mkNullableSome (← tm.mkInteger 5))
  let solver ← Solver.new tm
  value ← solver.simplify value
  assertEq false value.getBooleanValue!

  let tm' ← TermManager.new
  tm'.mkNullableIsNull (← tm.mkNullableSome (← tm.mkBitVectorOfString 3 "101" 2)) |> assertError
    "Given term is not associated with this term manager"

test![TestApiBlackTermManager, mkNullableIsSome] tm => do
  let mut value ← tm.mkNullableIsSome (← tm.mkNullableSome (← tm.mkInteger 5))
  let solver ← Solver.new tm
  value ← solver.simplify value
  assertEq true value.getBooleanValue!

  let tm' ← TermManager.new
  tm'.mkNullableIsSome (← tm.mkNullableSome (← tm.mkBitVectorOfString 3 "101" 2)) |> assertError
    "Given term is not associated with this term manager"

test![TestApiBlackTermManager, mkNullableNull] tm => do
  let nullableSort ← tm.mkNullableSort (← tm.getBooleanSort)
  let nullableNull ← tm.mkNullableNull nullableSort
  let mut value ← tm.mkNullableIsNull nullableNull
  let solver ← Solver.new tm
  value ← solver.simplify value
  assertEq true value.getBooleanValue!

  let tm' ← TermManager.new
  tm'.mkNullableIsNull (← tm.mkNullableNull (← tm.mkNullableSort (← tm.getBooleanSort)))
  |> assertError "Given term is not associated with this term manager"

test![TestApiBlackTermManager, mkNullableLift] tm => do
  let some1 ← tm.mkNullableSome (← tm.mkInteger 1)
  let some2 ← tm.mkNullableSome (← tm.mkInteger 2)
  let some3 ← tm.mkNullableLift Kind.ADD #[some1, some2]
  let solver ← Solver.new tm
  let three ← solver.simplify (← tm.mkNullableVal some3)
  assertEq 3 three.getIntegerValue!

  let tm' ← TermManager.new
  tm'.mkNullableLift Kind.ADD
    #[ (← tm.mkNullableSome (← tm.mkInteger 1)), (← tm.mkNullableSome (← tm.mkInteger 2)) ]
  |> assertError
    "invalid term in 'args' at index 0, expected a term associated with this term manager"

test![TestApiBlackTermManager, mkUniverseSet] tm => do
  tm.mkUniverseSet (← tm.getBooleanSort) |> assertOkDiscard
  tm.mkUniverseSet (Sort.null ()) |> assertError "invalid null argument for 'sort'"
  tm.mkUniverseSet (← tm.getBooleanSort) |> assertOkDiscard

  let tm' ← TermManager.new
  tm'.mkUniverseSet (← tm.getBooleanSort) |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkConst] tm => do
  let boolSort ← tm.getBooleanSort
  let intSort ← tm.getIntegerSort
  let funSort ← tm.mkFunctionSort #[intSort] boolSort
  tm.mkConst boolSort |> assertOkDiscard
  tm.mkConst funSort |> assertOkDiscard
  tm.mkConst boolSort "b" |> assertOkDiscard
  tm.mkConst intSort "i" |> assertOkDiscard
  tm.mkConst funSort "f" |> assertOkDiscard
  tm.mkConst funSort "" |> assertOkDiscard
  tm.mkConst (Sort.null ()) |> assertError "invalid null argument for 'sort'"
  tm.mkConst (Sort.null ()) "a" |> assertError "invalid null argument for 'sort'"
  tm.mkConst boolSort |> assertOkDiscard

  let tm' ← TermManager.new
  tm'.mkConst boolSort |> assertError "Given sort is not associated with this term manager"
