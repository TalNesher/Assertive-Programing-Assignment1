/*

Assertive Programming - Fall Semester 2024 - Lecture #4 (24/1/24)

Last week:

- (ghost) functions vs. (compilable, executable) methods
- recursive definition (in the spec) vs. iterative code (in the implementation)
- more on how to document proof obligations
- develop a method to compute the n-th Factorialonacci number, iteratively
- preconditions

Today:

- one more recursive definition (in the spec) vs. iterative code (in the implementation)
- more on how to document proof obligations: loop termination; a ghost method (= lemma);
  full documentation of the proof obligation
- (ghost) predicates

- in "ComputeFactorial2", using a "down loop", we can see an alternative approach to the design of a loop invariant,
  focusing on the gap between what's been already computed and the expected value

*/

ghost function Factorial(n: int): int
    requires n >= 0
{
    if n == 0 then
        1
    else
        n*Factorial(n-1)
}

ghost predicate Inv(n: int, i: nat, f: int) {
    n >= 0 && i <= n && f == Factorial(i)
}

// like a sequent in logic (natural deduction):
// n >= 0 |- Inv(n, 0, 1)
lemma ProofInit(n: int)
    requires n >= 0
    ensures Inv(n, 0, 1)
{}

lemma ProofPost(n: int, i: nat, f: int)
    requires Inv(n, i, f) && i == n
    ensures f == Factorial(n)
{}

lemma {:verify true} ProofLoopBody(n: int, i: nat, f: int, V0: int)
    requires V0 == n-i
    requires Inv(n, i, f)
    requires i != n
    ensures Inv(n, i+1, f*(i+1))
    ensures 0 <= n-(i+1) < V0
{}

method {:verify true} ComputeFactorial'(n: int) returns (f: int)
    requires n >= 0
    ensures f == Factorial(n)
{
    var i: nat;
    f, i := 1, 0;
    while i != n
        invariant Inv(n, i, f)
    {
        i := i+1;
        f := f*i;
    }
}

method {:verify true} ComputeFactorial(n: int) returns (f: int)
    requires n >= 0
    ensures f == Factorial(n)
{
    assert n >= 0;
    ProofInit(n);
    assert Inv(n, 0, 1);
    var i: nat;
    f, i := 1, 0;
    assert Inv(n, i, f);
    while i != n
        invariant Inv(n, i, f)
        decreases n-i
    {
        ghost var V0 := n-i;
        assert V0 == n-i;
        assert Inv(n, i, f);
        assert i != n;
        ProofLoopBody(n, i, f, V0);
        assert Inv(n, i+1, f*(i+1));
        assert 0 <= n-(i+1) < V0;
        i := i+1;
        assert Inv(n, i, f*i);
        assert 0 <= n-i < V0;
        f := f*i;
        assert Inv(n, i, f);
        assert 0 <= n-i < V0;
    }
    assert Inv(n, i, f) && i == n;
    ProofPost(n, i, f);
    assert f == Factorial(n);
}

ghost predicate Inv2(n: int, i: nat, f: int) {
    n >= 0 && i <= n && f*Factorial(i) == Factorial(n)
}

method {:verify true} ComputeFactorial2(n: int) returns (f: int)
    requires n >= 0
    ensures f == Factorial(n)
{
    var i: nat;
    f, i := 1, n;
    while i != 0
        invariant Inv2(n, i, f)
        //decreases i
    {
        f := f*i;
        i := i-1;
    }
}

method Main() {
	var f := ComputeFactorial(0);
	assert f == 1;
    print "0! = ", f, "\n";

	f := ComputeFactorial(1);
	assert f == 1;
    print "1! = ", f, "\n";

	f := ComputeFactorial(2);
	assert f == 2;
    print "2! = ", f, "\n";

	f := ComputeFactorial'(3);
	assert f == 6;
    print "3! = ", f, "\n";

	f := ComputeFactorial'(4);
	assert f == 24;
    print "4! = ", f, "\n";

	f := ComputeFactorial2(5);
	assert f == 120;
    print "5! = ", f, "\n";
}