# Peano tutorial

This is an introduction to the Peano language. As a language, Peano offers minimal syntax and no fancy usability features. The biggest value of Peano is as an environment for agents to find proofs automatically, which is done using the Python API. However, even for that use, you still interact a little bit with the language directly, at least in order to write axioms and theorem statements. Thus, in this tutorial, we will write a simple formalization of the natural numbers based on the Peano axioms (in this case, Peano the logician), using the Peano language.

## Simple declarations

There are only three kinds of statements in a Peano file: imports, declarations and proofs. Let's first look at declarations. Declarations create a new object, and we provide its name and type. There are two base types: `type` (the type of types) and `prop` (the type of propositions). In Peano, a declaration has the syntax `name : dtype.`, where `name` is any identifier (which can contain letters, numbers and signs, like `+`, `-` or `/`, so you can use the usual operator symbols as names), and `dtype` is a type expression. A declaration ends in a period. Let's first declare the natural numbers as a type:

```
nat : type.
```

So we now have a type named `nat`, but it has no structure at all attached to it. In particular, we still have no natural numbers, or ways to construct them. In theorem proving languages based on the Calculus of Inductive Constructions, we'd normally declare the type `nat` along with its constructors - typically zero and the successor function. This automatically adds several axioms attached to the type. In Peano, we'll manually add in those axioms. First, let's declare zero as our first natural number:

```
zero : nat.
```

So now we have a natural number named `zero`. We'll also assume there is a function called `succ`, which takes a natural number and returns another one (its successor). Functions in Peano have function type, which we write in curried syntax as `[t1 -> t2]`, for a function taking an argument of type `t1` and producing a result of type `t2`. If we wanted more arguments, we'd chain their types in arrows, as `[t1 -> t2 -> t3]`. So here is how we'd state the existence of the successsor function:

```
succ : [nat -> nat].
```

Note that both `zero` and `succ` have no *value*: we're simply saying "there exists an object called `zero` of type `nat`, and there exists a function `succ` that takes a natural number and produces another", but we need not say anything about what `zero` and `succ` really do. Thus, these are *opaque* objects, which have no value associated with them, only their types. We can also declare an object that has a name and a value. For example:

```
one : nat = (succ zero).
```

Here, `one` is also a natural number, but we also say that it is the successor of zero, explicitly. Thus, from now on, the name `one` and the expression `(succ zero)` (the function `succ` applied to the argument `zero`) are *definitionally equal* - they are equivalent in any context. We can also declare functions by giving their body as a lambda expression. For example:

```
succ_twice : [nat -> nat] = (lambda ('x : nat) (succ (succ 'x))).
```

Thus, this declares a function named `succ_twice`, but not an opaque one, since we provide its body. Namely, this function takes one argument named `'x`, of type `nat`, and applies `succ` twice to it. Arguments to functions (or to types, as we'll see soon) need to start with a single quote, and are bound in the scope inside the lambda (or, later, the type declaration).

We now have ways to construct natural numbers. We haven't said much about them yet, but we have enough to prove our first simple theorems about them. Let's do that first, and then add some more to our natural numbers.

So far, this is what we have:

```
nat : type.
zero : nat.
succ : [nat -> nat].

one : nat = (succ zero).
succ_twice : [nat -> nat] = (lambda ('x : nat) (succ (succ 'x))).
```

We can save this in a file, say `nats.p`, and run it through Peano with:


```bash
[gpoesia@gabriel-notebook environment]$ target/release/peano nats.p 
Loading nats.p
No proofs found.
```

So our declarations were accepted, but we haven't tried to prove anything yet. Let's do that now.

## Equality

Peano has a built-in notion of *propositional* equality - the mathematical statement that two objects are equal. However, the intrinsics that come with equality right now are activated once we declare the equality predicate. Let's do that:

```
= : [('t : type) -> 't -> 't -> prop].
```

This declares a new object, named `=`, which has a dependent type. Namely, its first argument is a type, called `'t`. Then, it takes two objects of type `'t`, and produces a *proposition* asserting that those two objects are equal. Note that a proposition is merely a mathematical statemement - the kind of thing that can be true (if we provide a proof of it).

How do we prove that two things are equal? Equality predicate comes with two intrinsic axioms that will let us do that. The first is reflexivity, called `eq_refl`: any object is equal to itself. If we wanted, we could state reflexivity ourselves as follows:

`our_eq_refl : [('t : type) -> ('obj : 't) -> (= 'obj 'obj)].`

This reads: for any type `'t`, for any object `'obj` of type `'t`, the axiom `our_eq_refl` gives an object of type `(= 'obj 'obj)`. This is a proposition type, thus, under the Curry-Howard correspondence, an object of this type is interpreted as evidence (a "proof") that this proposition is true. Since we're just saying that `our_eq_refl` exists and provides such evidence without saying how, this is an axiom: any object of any type is equal to itself.

If you have been following closely, one detail might be odd: when we declared equality, it had three arguments, but in `(= 'obj 'obj)` it seems like we're only providing two. Peano lets the first argument to equality be *implicit*, since it can be inferred from the second and third argument (`'t` has to be whatever type the objects passed as later arguments have). While this is a nice feature to have in general (allowing implicit arguments), right now Peano only offers this for the built-in equality type, since it is ubiquitous. This is, however, a possible extension for the future, if Peano indeed proves useful as an environment for proof search.

Besides reflexivity, the other defining axiom about equality is that we can substitute equal objects for one another in any context. This is implemented in Peano as a built-in `rewrite` axiom, that we will use extensively in proofs.

## Our first proofs

Let's prove our first theorem. We should be able to easily prove that the natural number `zero` is equal to itself. Let's do that:

```
nat : type.
zero : nat.
succ : [nat -> nat].

one : nat = (succ zero).
succ_twice : [nat -> nat] = (lambda ('x : nat) (succ (succ 'x))).

= : [('t : type) -> 't -> 't -> prop].

lemma zero_eq_zero : (= zero zero) {

}
```

This is declaring an object named `zero_eq_zero`, which has type `(= zero zero)`. However, since we declare it as a `lemma` (which could also be `theorem` or `corollary`, with no semantic difference), we are saying we will provide its proof, not just accept it as an axiom. Right now, of course, the proof is empty. If we try to run the file so far, we get:


```bash
[gpoesia@gabriel-notebook environment]$ target/release/peano nats.p zero_eq_zero
Loading nats.p
Verifying zero_eq_zero... error: Proof goal is still open: (= zero zero)
Error: "Proof goal is still open: (= zero zero)"
```

Note that we passed the name of the lemma we wanted to check as a second argument to the Peano executable. The output says that so far, the proof is correct (we haven't tried anything yet to risk failing!), but it is incomplete: we have "one open goal". The goal is the type of the object we are trying to construct. How should we do that? We'll use the `eq_refl` axiom. One line suffices:

```
lemma zero_eq_zero : (= zero zero) {
    show (= zero zero) by eq_refl.
}
```

Now we get:

```bash
[gpoesia@gabriel-notebook environment]$ target/release/peano nats.p zero_eq_zero
Loading nats.p
Verifying zero_eq_zero... ok
```

Meaning our proof is complete.

Note that reflexivity is a bit more powerful than it might seem, because it can resolve definitional equalities automatically. This means that values that are known are seen to be equivalent to the names they are given. Thus, for instance, we could also prove the following lemma by reflexivity:

```
lemma example_2 : (= (succ one) (succ_twice zero)) {
    show (= (succ one) (succ_twice zero)) by eq_refl.
}
```

## Using assumptions and equalities

Let's prove a slightly more interesting theorem about the natural numbers and equality. We'll prove that equality is *symmetric* (if `a = b`, then `b = a`) and *transitive* (if `a = b` and `b = c`, we'll show `a = c`). For that, we'll need to use `rewrite`, and also to take assumptions.

Let's start with symmetry. The theorem statement looks like this:

```
lemma nat_eq_symm : [('x : nat) -> ('y : nat) -> (= 'x 'y) -> (= 'y 'x)] {

}
```

This reads: for all natural numbers `'x` and `'y`, if we have a proof that `(= 'x 'y)`, we'll show how to prove `(= 'y 'x)`. Our proof goal is universally quantifying over natural numbers `'x` and `'y`. Our first move will be to say "Let x and y be arbitrary natural numbers". We'll do that with `intro` statements:

```
lemma nat_eq_symm : [('x : nat) -> ('y : nat) -> (= 'x 'y) -> (= 'y 'x)] {
    intro a : nat.
    intro b : nat.
}
```

Initially, our goal was to prove something about all natural numbers `'x` and `'y`. Now that we assumed two particular natural numbers `a` and `b`, our goal is simply to prove that if `a = b`, then `b = a` for these two particular numbers (the names `a` and `b` were arbitrary here, but notice that we should not use a single quote since they are not quantified anymore). Our goal has changed, and we can make the new goal explicit with a `current goal` statement:

```
lemma nat_eq_symm : [('x : nat) -> ('y : nat) -> (= 'x 'y) -> (= 'y 'x)] {
    intro a : nat.
    intro b : nat.
    current goal : [(= a b) -> (= b a)].
}
```

"current goal" doesn't change anything - it will simply verify that the goal we typed out is indeed the proof goal at that point. This is a simple feature to make proofs easier to look at, and it corresponds to the statements we write on paper proofs "[...] We now have to prove that X holds. [...]", except that it is checked by the runtime.

What now? We now will introduce the assumption that `a` is equal to `b`. To do that, we'll use the exact same mechanism we used to introduce `a` and `b`:

```
lemma nat_eq_symm : [('x : nat) -> ('y : nat) -> (= 'x 'y) -> (= 'y 'x)] {
    intro a : nat.
    intro b : nat.
    current goal : [(= a b) -> (= b a)].

    intro h : (= a b). /* Assume a = b. Let's call this assumption h. */
    current goal : (= b a). /* We now have to prove b = a. */
}
```

Note that the comments as written above are valid Peano code. Comments can span multiple lines. If we run our current proof, we'll get the error saying that the proof goal is still open. But the goals are indeed as we have written (you can try messing with those and seeing the error you get).

OK, now we finally got to the meat of our proof. How should we show `(= b a)`? So far we only have two tools at our disposal: `eq_refl` (which we have seen) and `rewrite` (which we'll use for the first time). Indeed, we'll use a combination of both. The idea of the proof will be to first show that `a = a` by reflexivity, and then argue that, since we have `a = b` by assumption, we can substitute the first `a` in `a = a` by `b`, obtaining a proof that `b = a`. In Peano, it will suffice to say:

```
lemma nat_eq_symm : [('x : nat) -> ('y : nat) -> (= 'x 'y) -> (= 'y 'x)] {
    intro a : nat.
    intro b : nat.
    current goal : [(= a b) -> (= b a)].

    intro h : (= a b). /* Assume a = b. Let's call this assumption h. */
    current goal : (= b a). /* We now have to prove b = a. */
    
    show (= a a) by eq_refl.
    show (= b a) by rewrite.
}
```

Since our goal was to show `(= b a)`, we are done:

```
[gpoesia@gabriel-notebook environment]$ target/release/peano nats.p nat_eq_symm
Loading nats.p
Verifying nat_eq_symm... ok
```

Note that there is nothing special about natural numbers that allowed us to prove this theorem. We could actually generalize it to any type:

```
lemma eq_symm : [('t : type) -> ('x : 't) -> ('y : 't) -> (= 'x 'y) -> (= 'y 'x)] {

}
```

The proof is left as an exercise. It will only require one extra step and minor changes to the one above for natural numbers.

Transitivity of equality can be proven with the same basic moves.

```
lemma eq_trans : [('t : type) -> ('x : 't) -> ('y : 't) -> ('z : 't) -> (= 'x 'y) -> (= 'y 'z) -> (= 'x 'z)] {

}
```

Let's start by taking in all of the assumptions:

```
lemma eq_trans : [('t : type) -> ('x : 't) -> ('y : 't) -> ('z : 't) -> (= 'x 'y) -> (= 'y 'z) -> (= 'x 'z)] {
    intro t : type.
    intro x : t.
    intro y : t.
    intro z : t.
    intro h1 : (= x y).
    intro h2 : (= y z).
}
```

Our goal now is to show `(= x z)`. Can you spot how this will follow? This will only take one step: we can use h2 to substitute y for z in h1. This immediately gives `(= x z)`. We can simply add this last step to the proof:

```
    show (= x z) by rewrite.
```

And we're done:

```bash
[gpoesia@gabriel-notebook environment]$ target/release/peano nats.p eq_trans
Loading nats.p
Verifying eq_trans... ok
```

## Backward actions

*TODO*

## Completing the Peano axioms

*TODO*
