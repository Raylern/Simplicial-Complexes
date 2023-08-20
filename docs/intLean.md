# Introduction to Lean

author: Ray Zhan		 email : ray1710852730@163.com 



Introduction 

Geometric group theory

cayley graph

negatively curved group

free group

[TOC]



## Introduction

Lean is a functional programming language, and is mainly used as an interactive theorem prover. And its syntax is similar to LISP and the language that mathematicians use.

* first-class functions
* pattern matching (mgu, ...)
* type inference
* extensible syntax
* meta-programming
* object oriented programming (polymorphic, )
* symbolic programming (eval, expressions, ...)



### Anatomy



##### Comments

`-- comment` comment a line

`/- comment -/` comment box





### Files

`import`



#### Semantics

**semicolon** `;` means "do the next tactic in the same time as the previous one", and it doesn't mark the end of a clause, possible to have several semicolons.

underline `_` askes Lean to try to figure out the parameters itself.

`tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal, concatenating all goals produced by `tac'`

`*`, `at *` targets all the hypothesis and the goals

`"`, function apply at each elements in a set and returns a set



##### brackets



|        |                                                              |                                                              |
| ------ | ------------------------------------------------------------ | ------------------------------------------------------------ |
| `()`   | * explicit arguments or 'assumptions'<br />* change order of operation | Explicit binder.                                             |
| `{}`   | implicit arguments that will not really provided in application, and left for Lean's unifier to find out, equivalent as putting `_` | Implicit binder. In regular applications without `@`, this argument is automatically inserted and solved by unification whenever all explicit parameters before it are specified. |
| `{{}}` | implicit arguments that will not really provided in application | Strict-implicit binder. In contrast to `{}` regular implicit binders, a strict-implicit binder is inserted automatically only when at least one subsequent explicit parameter is specified. |
| `[]`   | * list delimiter<br />* arguments (usually proofs about instances) that will not be provided, and left for Lean to search in the library among those with `instance` tags | Instance-implicit binder. In regular applications without `@`, it is automatically inserted and solved by typeclass inference of the specified class. |



for example,

```
add_comm : ∀ {G : Type} [_inst_1 : add_comm_semigroup G] (a b : G)
	:= a + b = b + a
#check add_comm a b
```

* The `add_comm` function was given `a` and `b`
* Lean knows that `a` has type `ℝ` because that’s part of the definition of `a`. So the unifier figures out that `G` must be `ℝ`. 
* The one remaining input to the function is a variable with the weird name of `_inst_1`, whose type is `add_comm_semigroup ℝ`, which is a proof that the reals are an additive commutative semigroup. The inference system search in the library an find the proof tagged `@[instance]` and fills in.



>  `{}` vs. `⦃⦄` 
>
>  `{}` is more *eager* than `{{}}`. This is all about the exact timing of the unifier. Basically if you have `f (a : X) {b : Y} (c : Z)` and `g (a : X) ⦃b : Y⦄ (c : Z)` then the unifier will attempt to figure out `b` in `f` the moment you have given it `f a`, but it will only start worrying about `b` in `g` when you have given it `g a c`.

play with this code: [brackets.lean](./resources/brackets.lean)



references : 

[6. Interacting with Lean — Theorem Proving in Lean 3.23.0 documentation (leanprover.github.io)](https://leanprover.github.io/theorem_proving_in_lean/interacting_with_lean.html#more-on-implicit-arguments)

[Brackets in function inputs (imperial.ac.uk)](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2022/Part_B/brackets.html)



### Lean vs LISP

Lean language shares some similarity with LISP language.

function application `(f a)`

cas and cds `(a b).1`, `(a b).2`







## Programming Side



### Commands

##### Auxiliary Commands

**Auxiliary commands** are commends that query the system for information typically begin with the hash `#` symbol.

|                |      |                               |
| -------------- | ---- | ----------------------------- |
| `#check <id>`  |      | check the type                |
| `#print <str>` |      | print a string or description |
| `#eval <expr>` |      | evaluate expression           |



### Scopes

#### Namespace

namespace provides a ways to group identifiers with hierarchy.

* Can be nested
* Namespaces that have been ended can later be reopened, even in another file. However, no collisions allowed in definition of identifiers.

To access an identifier in a namespace. Use `.` operator, as `<namespace_id>.<id>`.

~~~
namespace Test
	def a : Nat := 5
end Test

#check a
-- #check b -- error, since not declared yet

-- the following can also be written in another file
namespace Test
	def b : Nat :=520
	-- def a : Nat :=1314 -- error, since already declared
end Test

#check a
#check b
~~~

##### Command::open

`open <namespace_id>` adds the `<name_space_id>` to a queue. And when finding an identifier, it searches in the namespaces in the queue according to the order. 

Thus, when an identifier appears in several opened namespaces, the first definition according to the order in queue will be used.



play with this code: [nest_namespaces.lean](./resources/nest_namespaces.lean)





#### Section



> **Namespace vs. section**
>
> Namespaces and sections serve different purposes,
>
> * namespaces organize data and sections declare variables for insertion in definitions. 
> * sections are also useful for delimiting the scope of commands such as `set_option` and `open`.
>
> In many respects, however, a `namespace ... end` block behaves the same as a `section ... end` block.
>
> In particular, if you use the `variable` command within a namespace, its scope is limited to the namespace. Similarly, if you use an `open` command within a namespace, its effects disappear when the namespace is closed.



### Types

Type is the key concept in Lean. Types are first-class citizens in Lean.



###### subType builder

``{<var> : <type> // <properties>}`` constructs a subtype.

Any terms of this subtype will automatically have 2 attributes

* `<var>.val` : the underlying type
* `<var>.property` : the properties



#### Type theory

**Type** is similar to a set, the things in the type are called **terms**.

|      |         |          |
| ---- | ------- | -------- |
| set  | element | $A\in B$ |
| type | term    | $A:B$    |

* Simple Type Theory: every expression has an associated type

* Dependent Type Theory: types themselves (entities like `Nat` and `Bool`) are first-class, which is to say that they themselves are objects and can be used to construct other types.

    > Example
    >
    > ~~~
    > #check Nat   --Type
    > #check Type  --Type 1
    > ~~~
    >
    > We will see what is `Type 1` later.

In type theory, a **property** or **predicate** on a type $\alpha$ is just a function $P : \alpha \to Prop$.

For example, given `a : α`, $P$ a is just the proposition that $P(a)$ holds. In the library, `Set \alpha` is defined as a term in type `α -> Prop  ` and `x \in s` is defined to be `s x`. In other words, sets are really properties, treated as objects.  

Lean’s type theory is suggesting an interesting model, that a proposition is a type (set) with at most one term (element). If the set has an element, it corresponds to a true statement, and if it has no elements then it corresponds to a false statement.

In Lean, there is a **universe** of all 'usual' types like `Nat`, `Prop`, this universe is called `Type` or `Type 0`. (A universe is a closure of a set/type `S`, corresponding to a set of operations $op_n:\hat{S}^n \to \hat{S}$ like `List`, `Prod`, `fun`)

> Example
>
> ```
> #check fun Nat=>Nat -- Type (Nat : Type 0)
> ```

> **Larger universe**
>
> Notice that `Type` (`Type 0`) itself should be a type (due to simple type theory in Lean), but, it is not in the universe `Type` (it is similar that $\N$ is the set of natural number, but $\N$ itself is NOT a natural number). What should be the type of `Type` (Which universe does it live in) ?
>
> Lean solves it in a smart way. Which leads to **universe** of all 'usual' types like `Nat`, `Prop`, and in addition, `Type 0`, which is called `Type 1`. And this can be continued to `Type n`
>
> ~~~
> #check Nat \times Nat  				--Type
> #check Type -> Nat \times Nat 		--Type 1
> #check Type 1                       --Type 2
> #check Type 2 -> Type 1 \times Type --Type 3
> ~~~
>
> And one can use `Type _` to be referring to an arbitrary type. (Although Type of all types is not a type) 



> Built-in Types always begins with a capital letter



##### Nat

a Lean natural number is an arbitrary-precision unsigned integer.

> Nat in Lean contains 0.



##### Prop

In Lean, the collection of all true-false (provable-unprovable) statements forms a universe called `Prop`, which all propositions are of this type

~~~
#check a > 0 -> a \le 0     -- Prop
~~~

The idea that a proposition can be thought of as a type means in particular that a proposition has somehow got “elements”.

The “elements” (or, to use Lean’s language, the terms) of a proposition are its proofs! Every proposition in Lean has *at most one term*. The true propositions have one term, and the <strike>false</strike> unprovable propositions have no terms



##### Functions

functions are first-class in Lean.



##### finite types

`Fin n` can be iterated by `\forall`, 

`{ v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }`



##### Product types



##### Sigma types

`\Sigma n : \N, StandardSimplex n`,

a generalized tuple (possibly an infinite tuples)

Given `s : StdSimplex`, the first component `s.fst` is a natural number, and the second component `s.snd := StandardSimplex s.fst` is an element of the corresponding simplex `StandardSimplex s.fst`. The difference between a Sigma type and a subtype is that the second component of a Sigma type is data rather than a proposition  





##### structure and field





#### Structures & Classes



* defining a structure :

    ```
    @[<tags>]
    structure <id> where
    	<field_id> : <type>
    ```

    > A structure is a type, and, usually, a type is a structure.
    >
    > An instance of a structure is a term of the type

    > `@[ext]` annotation tells Lean to automatically generate theorems that can be used to prove that two instances of a
    > structure are equal when their components are equal

* defining an instance : 

    default constructor : `<id>.mk`  

    ```
    def <instance_id> : <struct_id> where
      <field_id> := <value>
    ```

    ```
    def <instance_id> : <struct_id> :=
      \< vals \>
    ```

    ```
    def <instance_id> :=
      <struct_constructor> (vals)
    ```

    >Values are just terms of some types

    >The first 2 ways need to specify the structure. And the anonymous constructor (`\<\>`) will call the struct constructor

    > A 'name' can be associated to the constructor by
    >
    > ```
    > structure <id> where <constructor_name> ::
    >   <field_id> := <value>
    > ```

* function/method of a structure

    > anonymous projection notation, which allows us to write `<instance_id>.<func> <args>` instead of `<struct_id>.<func> <instance_id> <args>`. Lean interprets the former as the latter because of type inference.  

* adding/assuming structure to objects

    ~~~
    example (\a : Type) [Group \a] : ...
    ~~~

    

* a

> a remark about type inference
>
> 

`protected` keyword 'fix' the name of the theorem to be `<id>.<func>`, even when the namespace is open. This is helpful when we want to avoid ambiguity with a generic theorem like `add_comm` (which is defined in `Nat`, `Real` and many places)





* distrib
* commut
* preorder
* partial_order

adding additional structure to a variable

```
variable (A : Type _) [AddGroup A]
#check (add_assoc : 8 a b c : A, a + b + c = a + (b + c))
#check (zero_add : 8 a : A, 0 + a = a)
#check (add_left_neg : 8 a : A, -a + a = 0)
```

> setting attributes can make simp knowing the rules for simplifying



#### Classes

`\mathematics_in_lean\lake-packages\mathlib\Mathlib\Algebra\Group\Defs.lean`

* recognition of instances of structures.

    > For example
    >
    > The number systems $\Z$, $\Q$, and $\R$ are all ordered rings, there should be a generic theorem / function about ordered rings in any of these instances. 

* structures can inherit/extend from other structures. Some structures extend others by adding more axioms.

    

* 

* Support a set of generic notations on structures

    the notation `*` is used for multiplication in a relavent structure.

    > 

    

    

    > For example
    >
    >  in addition to the usual topology on $\R$, which forms the
    > basis for real analysis, we can also consider the discrete topology on $\R$, in which every set is open.  

    

Third, it needs to deal with the fact that 

> It is sometimes useful to bundle the type together with the structure  
>
> ```
> structure GroupCat where
> 	α : Type _
> 	G : Group α
> ```
>
> It is more often useful to keep the type `α` separate from the structure `Group
> α`. The two objects together are called **partially bundled structure** as an representation for mathematical object. The representation bundles most (but usually not all) of the components into one structure. It is common in `mathlib` to use capital roman letters like `G` for a type when it is used as the carrier/container type (such as `GroupCat`) for a group.  





> Classes vs Structures
>
> 





Examples of some mathematical structures

| structure | definition |      |
| --------- | ---------- | ---- |
| `Group`   |            |      |
|           |            |      |
|           |            |      |





##### Set

library relavant : `Mathlib.Data.Set`

**Set** is one of the most basic mathematical structure.



###### Set builder

The library `Set` defines a set-builder notation. 

The expression `{ y | P y }` unfolds to `(fun y \mapsto P y)`, so `x \in { y | P y }` reduces to `P x`.

Set-builder notation is used to define some sets

* $s\cap t$ as $\{x | x \in s \and x \in t\}$,
* $s\cup t$ as $\{x | x \in s \or x \in t\}$,
* $\emptyset$ as $\{x|False\}$
* `univ` as $\{x | True\}$    

Lean unfolds the last two definitions automatically when needed.

> `trivial` is the canonical proof of `True` in the library ,
>
> thus it solves `x \in univ`. 
>
> ```
> example (x : ℕ) : x ∈ (univ : Set ℕ) :=
>   trivial
> ```
>
> 



###### Indexed union & intersection

Given a sequence (indexed collection) $\{A_i\}_{i\in I}$ of sets of terms in type $\alpha$ as a function $A : N \to Set(\alpha)$, (`i : I` is assumed) in which case

* `⋃ i, A i` denotes their union
* `⋂ i, A i` denotes their intersection.  

Parentheses are often needed with an indexed union or intersection because, as with the quantifiers, the scope of the
bound variable extends as far as it can.  

`mathlib` also has bounded unions and intersections, which are analogous to the bounded quantifiers. You can unpack their meaning with `mem_iUnion2` and `mem_iInter2`.  



Give a set (collection) of sets, $S: Set(Set(\alpha))$, their union, $⋃_0 S$, has type $Set (\alpha)$ and is defined as $\{x | \exists T \in
S, x \in T\}$. Similarly, their intersection, $⋂_0 S$, is defined as $\{x | \forall T \in S, x \in T\}$. These operations are called
`sUnion` and `sInter`, respectively.

Their definition can be unpacked by `mem_iUnion2` and `mem_iInter2`.





 

##### Lattice

**Lattice** is a structure that extends a partial order with operations $\sqcap$ and $\sqcup$.

* $\sqcap$ is the greatest lower bound, infimum, or meet. `\glb`
* $\sqcup$ is the least upper bound, supremum, or join. `\lub`



> proposition `P`,`not P` is implimented as `P \implies false`, which is a 'function'
>
> ~~~
> open classical
> 
> axiom not_iff_imp_false (P : Prop) : ¬ P ↔ (P → false)
> 
> lemma contrapositive (P Q : Prop) :  (¬ Q → ¬ P) → (P → Q)  :=
> begin
> intro nqnp,
> intro p,
> by_contra nq,
> have np : ¬P :=  nqnp(nq),
> show false, from np p,
> end
> ~~~
>
> but `p np` won't work.
>
> proposition `P,Q`, `P↔Q` is implemented as `(P\implies Q) \and (Q\implies P)`.



##### Set theoretical functions

library relavant : `Mathlib.Data.Set.Function`

* evaluation : `f x`
* preimage : `preimage f p`, written `f\inv p`, is defined by the set builder to be `{x | f x \in p}  `
* image : `image f s`, written `f '' s`, is defined by the set builder to be `{y | \exists x, x \in S
    \and f x = y}`  

###### properties of functions

Library defines a predicate `InjOn f s` to say that $f$ is injective on set $s$. The statement `Injective f` is provably equivalent to `InjOn f univ`.   

```
example : InjOn f s $ 8 x1 2 s, 8 x2 2 s, f x1 = f x2 ! x1 = x2 :=
	Iff.refl _
```

| predicate      | definitionally equivalent                                    | provably equivalent |
| -------------- | ------------------------------------------------------------ | ------------------- |
| `domain`       |                                                              |                     |
| `codomain`     |                                                              |                     |
| `Injective f`  | ` \forall x1 \in s, \forall x2 \in s, f x1 = f x2 -> x1 = x2  ` | `InjOn f univ`      |
| `Surjective f` | `∀ (b : β), ∃ a, f a = b`                                    | `β \subset range f` |
| `range f`      | `{x |\exists y, f y = x}`                                    | `f '' univ  `       |
|                |                                                              |                     |



To define the inverse of a function `f : α -> β`, we will use two new ingredients.

* an arbitrary type in Lean may be empty. To define the inverse to $f$ at $y$ when there is no $x$ satisfying `f x = y`, we assign a default value. Adding the notation `[Inhabited α]` as a variable to assume a preferred element in $\alpha$ as default. 
* where there is more than one $x$ such that $f x = y$, the inverse function needs to choose one of them. This requires an appeal to the axiom of choice. Lean allows various ways of accessing it. one convenient method is to use the classical `choose` operator.

```
variable {α β : Type _} [Inhabited α]
#check (default : α)

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default
```



##### Type vs Set

Type theory generalizes set theory.

> **Propositional implication = Function **
>
> In Lean’s type theory we say it like this: if `X` and `Y` are types in the `Type` universe, then we can consider the type `X → Y` of functions from `X` to `Y`, and a term `f : X → Y` of this type is a function from `X` to `Y`.
>
> In usual mathematical logic, we might say the following: If `P` and `Q` are propositions, then `P ⇒ Q` is also a proposition. If we have a hypothesis/proof `h` that says that `P ⇒ Q` is true, we might write `h : P ⇒ Q`.
>
> In Lean’s type theory, if `P` and `Q` are types in the `Prop` universe, i.e., propositions, then 
>
> * `P → Q` is a type of functions from proofs of `P` to proofs of `Q`.
> * `P ⇒ Q` is a propositional implication. Which can be thought as a type whose terms are its proofs.
> * If we have such a function `h:P → Q`, which takes as input a proof of `P` and spits out a proof of `Q`, then `h` can be thought as a proof of proposition `P ⇒ Q`.
> * So, In Lean the function type `P → Q` lives in the `Prop` universe – it’s also a true-false statement. (`P ⇒ Q`) is the 'same' as (`P → Q`)



#### Attributes

objects like `theorem`, `class` can be associated with some attributes. 

* `attribute [<attr1>,...]`,`@[<attr1>,...]`. Most of these commands are by default global. They remain in effect not only in the current file, but also in any file that imports it
* `local attribute [<attr1>,...]`. With the `local` modifier, one can make the attribute only affect until the current `section` or `namespace` is closed.

Adding attributes may be useful for,

* let some tactics automatically use the objects with certain attributes, like `@[simp]`
* some attribute automatically adds methods to the object, like `@[ext]` 

|                     |                                                         |      |
| ------------------- | ------------------------------------------------------- | ---- |
| `simp`              | objects that can be used by `simp` tactics              |      |
| `ext`               | automatically generates `<id>.ext` methods for equality |      |
| `rfl` (lean3)       | objects that can be used by `rfl`                       |      |
| `instance ` (lean3) |                                                         |      |
| `class` (lean3)     |                                                         |      |



##### default element

defining an default term in a type

`instance : Inhabited <class_id> where default := <default_ins>`

> Notice that defining a default term is just creating an instance in class `Inhabited (α: Type _)` and binds the name (constructor) default to it. 
>
> The Lean library defines a class
> `Inhabited α`, which does nothing more than store a default value.  

`(default : Point)` or `default`(and type inference can be done) will refer to the default element.



default element has many uses, for example

* function `List.headI`, which returns the first
    element of a list, can return the default value when the list is empty.  

    ~~~
    example : ([] : List Point).headI = default :=
    	rfl
    ~~~

* a





#### Operator overloading

operators in Lean are just representations of some class of operations

The expression `x + y` is an abbreviation for `Add.add x y`, where `Add α` is a class that stores a binary function on `α`.  

Writing `x + y` tells Lean to find a registered instance of `[Add.add α]` and use the corresponding function in the class `α`. We register the addition function for a class/type by creating an instance of the class.

```
instance : Add <class_id> where add := <func>
```



Here are some operators and notations,

|          |               |       |               |
| -------- | ------------- | ----- | ------------- |
| `Add α ` | `α -> α -> α` | `a+b` | `Add.add a b` |
| `Mul α`  | `α -> α -> α` |       |               |
| `Neg α`  | `α -> α`      |       |               |
| `Inv α`  | `α -> α`      |       |               |
| `Zero α` | `α`           |       |               |
| `One α`  | `α`           |       |               |







## Proving Side

### Terminology

* goal

* definition

* definitional equality : 2 expressions are equivalent by definition. 

    for definitional equality, no need to use `rw` explicitly. Lean can switch between the equivalent expressions automatically.

    > example
    >
    > in `Set.subset_def`, `(s ⊆ t) = ∀ (x : α), x ∈ s → x ∈ t`

* theorem / lemma

* example

* proof

* proof state



to define statement / notion,

~~~
def <id> (<param> : <type>): <body> := <proof>
~~~





### Tactics



`by` will creates a **tactics space** in which it runs all the tactics sequentially. And generates a term (usually a proof) of given type

Proof state is like a world. And tactics are like transitions between worlds

* hypothesis / proposition

    one cannot add hypothesis in the proof state freely. Usually, to add a hypothesis, one need to provide a prove

    > for example, using `have`
    >
    > ```
    > have <hypo_id> : <body>
    > \. <proof>
    > ```

    

* definition / term

    but adding a definition is easier

    > for example, using `let`
    >
    > ~~~
    > let <term_id> : <type> := <def>
    > ~~~

    

most tactics act on the first goal by default. If you want to apply to a hypothesis, you need to write `at <hypo_id>`. (or some may use `[<hypo_id>]`)



`trivial` is the canonical proof of `True` in the library  



##### Rewrites

|                               |                                                              |                                           |
| ----------------------------- | ------------------------------------------------------------ | ----------------------------------------- |
| `rw [ <hypo>] (at <hypo_id>)` |                                                              | Hypothesis are equivalences or equalities |
| `rwa [<hypo>]`                | calls `rw`, then closes any remaining goals using `assumption` |                                           |
|                               |                                                              |                                           |





|                                           |      |      |
| ----------------------------------------- | ---- | ---- |
|                                           |      |      |
| repeat {\<clauses>}                       |      |      |
| induction \<param> with \<hparam> \<hypo> |      |      |
| symmetric                                 |      |      |
| exact \<expr>                             |      |      |
| intro \<param> (intros \<params>)         |      |      |
| revert \<param>                           |      |      |
| have \<goal> \<proof>                     |      |      |
| apply \<rule>                             |      |      |



##### Dealing with Logical operators

| operator                    | in Goal                          | in Hypothesis                                                | lex construct |
| --------------------------- | -------------------------------- | ------------------------------------------------------------ | ------------- |
| $\and$, ($\leftrightarrow$) | `constructor`                    | `<hypo_id>.1` and `<hypo_id>.2`, or `cases`, `rcases` with `\<A,B\>` | `\<A,B\>`     |
| $\or$                       | `left` and `right`, (`by_cases`) | `cases`, `rcases` with `(A|B)`                               | `(A|B)`       |
| $\rightarrow$, ($\neg$)     | `intro`                          | backward : `apply`<br />forward : `f n` (as functions)       |               |
| $\forall$                   | `intro`                          | `rcases`                                                     |               |
| $\exists$                   | `use`                            | `rcases`                                                     |               |
| $=$, ($\leftrightarrow$)    | `rfl`                            | `rw`                                                         |               |



##### Dealing with patterns

|                                       |                                                              |                                                              |
| ------------------------------------- | ------------------------------------------------------------ | ------------------------------------------------------------ |
| `if <hypo> then <expr1> else <expr2>` | `by_cases`, and<br /> `rw [dif_pos <proof>]`, `rw [dif_neg <proof>]` | rewrite into `<expr1>` if the `<hypo>` is proved positive, otherwise `<expr2>` if negative. |
|                                       |                                                              |                                                              |
|                                       |                                                              |                                                              |
|                                       |                                                              |                                                              |
|                                       |                                                              |                                                              |
|                                       |                                                              |                                                              |
|                                       |                                                              |                                                              |





#### Basic Tactics 

|          |      |                                                              |
| -------- | ---- | ------------------------------------------------------------ |
| `unfold` |      |                                                              |
| `apply`  |      | applies an a function with zero or more arguments by unifying the conclusion with the expression in the current goal, and creating new goals for the remaining arguments |
| `intro`  |      |                                                              |
| `exact`  |      |                                                              |

> Tactics like `unfold`, `apply`, `exact`, `rfl` and `calc` will automatically unfold definitions.
>
> Tactics like `rw`, `ring` an `linarith` will generally
>
> not unfold definitions that appear in the goal.



#### Proving Tactics

|                              |                                                              |                                                              |
| ---------------------------- | ------------------------------------------------------------ | ------------------------------------------------------------ |
| `rfl`                        |                                                              | equalities that are true by definition (in a very strong sense) |
| `contrapose` (`contrapose!`) | change goal to contrapositive form (`!` try to simplify and push negation inside) |                                                              |
| `contradiction`              | finding contradictory hypothesis to prove `false`            |                                                              |
| `by_contra`                  | prove by contradiction                                       |                                                              |
| `exfalso`                    | change the goal to `false`                                   |                                                              |
|                              |                                                              |                                                              |



#### Tactics that uses library automatically

|                    |                                                              |                                                              |
| ------------------ | ------------------------------------------------------------ | ------------------------------------------------------------ |
| `simp`             | simplify expressions using libraries with tag `[simp]`, and do `unfold` and `rfl`. | `simp only [...]` := simplify only by the given functions<br />`dsimp` := simplify only by definition<br />`simp?` := show the list of things used |
| `apply?`           | automatically search in the library and apply                |                                                              |
| `tauto` (`tauto!`) | prove true statements in propositional logic using constructive logic. ( `tauto!` uses classical logic and closes more goals) |                                                              |
| `linarith`         | prove any related to ordering                                |                                                              |
| `norm_num`         | solve concrete numeric goals                                 |                                                              |



##### Tactics that uses structures

|        |      |                   |
| ------ | ---- | ----------------- |
| `ring` |      | commutative rings |
|        |      |                   |
|        |      |                   |



#### Tactics that forks

|               |      |                                                 |
| ------------- | ---- | ----------------------------------------------- |
| `have`        |      | create subgoal                                  |
| `cases`       |      |                                                 |
| `rcases`      |      |                                                 |
| `by_cases`    |      | split into `h` and `\not h` into the assumption |
| `induction`   |      |                                                 |
| `constructor` |      |                                                 |





#### Layout

`calc` is a good way to organize the proof step by step. 

~~~
calc
|  <expr> = <expr> := by <command>
|  _      = <expr> := by <command>
|  ....
~~~

`have` can be used to create sub-goals. And after proving the sub-goal, it can be used as hypothesis later on.

~~~
have <hypo_id>:<hypo_body>
\. <proof>
   <proof>
~~~





## Appendix





### Logic

* world
* inference rules
* predicate



### Terminologies

* term
* expression
* instance



### Special Symbols & fonts

| Symbol    | Code                       | ASCII Alternative |                                    |
| --------- | -------------------------- | ----------------- | ---------------------------------- |
| $\to$     | `\->`, `\to`, `\r`, `\imp` | `->`              | function                           |
| $\mapsto$ | `\mapsto`                  |                   |                                    |
| $\times$  | `\times`                   |                   | cartesian product                  |
| $\_$      | `_`                        |                   | the previous output<br />auto fill |
| $\circ$   | `\comp`                    |                   |                                    |
| $\forall$ | `\all`, `\forall`          |                   |                                    |
| $\exists$ | `\exists`, `ex`            |                   |                                    |
| $|$       | `\|`, `\mid`               |                   |                                    |



> most operators like $\rightarrow$, $\^{}$ are right associative



#### font

|           |                         |      |
| --------- | ----------------------- | ---- |
| subscript | `\<char>` or `\_<char>` |      |
|           |                         |      |
|           |                         |      |

### Keywords

|            |      |      |
| ---------- | ---- | ---- |
| `axiom`    |      |      |
| `example`  |      |      |
| `theorem`  |      |      |
| `lemma`    |      |      |
| `variable` |      |      |

|             |      |      |
| ----------- | ---- | ---- |
| `section`   |      |      |
| `namespace` |      |      |
| `protected` |      |      |



### Lean3

#### Tactics

|                          |                            |      |
| ------------------------ | -------------------------- | ---- |
| rw \<rule> \<args>       |                            |      |
| rwa [\<assump>, \<rule>] | rewrite according to rules |      |

|                                           |      |      |
| ----------------------------------------- | ---- | ---- |
| repeat {\<clauses>}                       |      |      |
| induction \<param> with \<hparam> \<hypo> |      |      |
| symmetric                                 |      |      |
| exact \<expr>                             |      |      |
| intro \<param> (intros \<params>)         |      |      |
| revert \<param>                           |      |      |
| have \<goal> \<proof>                     |      |      |
| apply \<rule>                             |      |      |

|             |      |      |
| ----------- | ---- | ---- |
| left        |      |      |
| right       |      |      |
| split       |      |      |
| cases       |      |      |
| exfalso     |      |      |
| by_cases    |      |      |
| use \<expr> |      |      |

|                |                                                              |      |
| -------------- | ------------------------------------------------------------ | ---- |
| simp           |                                                              |      |
| cc             |                                                              |      |
| refl           |                                                              |      |
| tauto (tauto!) | `tauto` is supposed to only use constructive logic, but its big brother `tauto!` uses classical logic and hence closes more goals. |      |
| ring           |                                                              |      |

##### References and games

[Natural number game (imperial.ac.uk)](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/?world=4&level=8)
