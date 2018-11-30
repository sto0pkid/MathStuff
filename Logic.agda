module Logic where

open import Agda.Primitive

{-
Negation:
1. [](¬P) → ¬(<>P)
2. ¬(<>P) → [](¬P)
3. <>(¬P) → ¬([]P)
4. ¬([]P) → <>(¬P)  -- couldn't prove, probably not constructively valid



Identity:
1. [](P) → ¬(<>(¬P))
2. <>(P) → ¬([](¬P))
3. ¬(<>(¬P)) → []P   -- couldn't prove, probably not constructively valid
4. ¬([](¬P)) → <>P   -- couldn't prove, probably not constructively valid


Axioms:
1. P → []P                          -- N rule; asserted
2. [](P → Q) → ([]P → []Q)        -- K rule; tautologous
3. []P → P                          -- T rule; assuming reflexivity
4. []P → [][]P                      -- 4 rule; assuming transitivity
5. <>P → []<>P                      -- 5 rule; assuming symmetry & transitivity
6. P → []<>P                        -- B rule; assuming reflexivity, transitivity and N-rule
7. []P → <>P                        -- D rule; assuming reflexivity

 

-}



{-
_∘_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (B → C) → (A → B) → (A → C)
(g ∘ f) = λ x → g (f x)
-}

module BaseDefinitions where
 module Void where
  data ⊥ : Set where
  ω : ∀ {i} {A : Set i} → ⊥ → A
  ω ()
 open Void public

 module Negation where
  module Definition where
   open Void
   ¬ : ∀ {i} → Set i → Set i
   ¬ {i} A = A → ⊥

  module Properties where
   open Definition
   A→¬¬A : ∀ {i} {A : Set i} → A → ¬ (¬ A)
   A→¬¬A {i} {A} a ¬A = ¬A a

 module Implication where
  _⊃_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A ⊃ B = A → B

 module Sum where
  data _∨_ {i} {j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
   inl : A → A ∨ B
   inr : B → A ∨ B

  infixr 5 _∨_
  _⊹_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  _⊹_ = _∨_

 open Sum

 module Product where
  data Exists {i} {j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
   _,_ : (a : A) → (B a) → Exists A B

  syntax Exists A (λ x → e) = ∃ x ∈ A , e

  π₁ : ∀ {i j} {A : Set i} {B : A → Set j} → (p : (∃ x ∈ A , (B x))) → A
  π₁ (a , b) = a

  proj1 = π₁

  π₂ : ∀ {i j} {A : Set i} {B : A → Set j} → (p : (∃ x ∈ A , (B x))) → B (proj1 p)
  π₂ (a , b) = b

  proj2 = π₂


  _∧_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A ∧ B = ∃ x ∈ A , B

  first : ∀ {i j} {A : Set i} {B : Set j} → A ∧ B → A
  first (a , b) = a

  second : ∀ {i j} {A : Set i} {B : Set j} → A ∧ B → B
  second (a , b) = b

  _×_ : ∀ {i j} → Set i → Set j → Set (i ⊔ j)
  _×_ = _∧_

  infixr 5 _∧_

 module Relations where
  module BinaryRelations where
   module Definition where
    Rel₂ : ∀ {i j} → Set i → Set (i ⊔ (lsuc j))
    Rel₂ {i} {j} A = A → A → Set j

   module Properties where
    open Definition
    module Reflexivity where
     Reflexive : ∀ {i j} → {A : Set i} → Rel₂ {i} {j} A → Set (i ⊔ j)
     Reflexive {i} {j} {A} R = (x : A) → R x x

    module Symmetry where
     Symmetric : ∀ {i j} → {A : Set i} → Rel₂ {i} {j} A → Set (i ⊔ j)
     Symmetric {i} {j} {A} R = {x y : A} → R x y → R y x

    module Transitivity where
     Transitive : ∀ {i j} → {A : Set i} → Rel₂ {i} {j} A → Set (i ⊔ j)
     Transitive {i} {j} {A} R = {x y z : A} → R x y → R y z → R x z
     
    open Reflexivity public
    open Symmetry public
    open Transitivity public
    
    record Equivalence {i} {j} {A : Set i} (R : A → A → Set j) : Set (i ⊔ j) where
     field
      reflexive : Reflexive R
      symmetric : Symmetric R
      transitive : Transitive R
 
    module Antisymmetry where
     Antisymmetric : ∀ { i j k} → {A : Set i} → (_~_ : A → A → Set k) → Equivalence _~_ → Rel₂ {i} {j} A → Set ((i ⊔ j) ⊔ k)
     Antisymmetric {i} {j} {k} {A} _~_ ~-equiv R = {x y : A} → R x y → R y x → x ~ y
   open Properties public
  open BinaryRelations public
  



 module Equality where
  module Definition where
   open Negation.Definition
   data _≡_ {i} {A : Set i} (x : A) : A → Set i where
    refl : x ≡ x

   _≠_ : ∀ {i} {A : Set i} (x : A) → A → Set i
   x ≠ y = ¬ (x ≡ y)

  module Properties where
   open Definition
   open Relations
   [A≡B]→[A→B] : ∀ {i} {A B : Set i} → A ≡ B → A → B
   [A≡B]→[A→B] refl a = a

   ≡-sym : ∀ {i} {A : Set i} → Symmetric (_≡_ {i} {A})
   ≡-sym refl = refl

   ≡-trans : ∀ {i} {A : Set i} → Transitive (_≡_ {i} {A})
   ≡-trans refl refl = refl

   cong : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → {x y : A} → x ≡ y → (f x) ≡ (f y)
   cong f refl = refl

   transport : ∀ {i j} {A : Set i} → (P : A → Set j) → {x y : A} → x ≡ y → P x  → P y
   transport P refl Px = Px

   ≡-equiv : ∀ {i} {A : Set i} → Equivalence {i} {i} {A} _≡_
   ≡-equiv =
    record {
     reflexive = λ x → refl ;
     symmetric = ≡-sym ;
     transitive = ≡-trans 
    }

   
  open Definition
  open Properties

 module Biimplication where
  module Definition where
   open Product
   _↔_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
   A ↔ B = (A → B) ∧ (B → A)

 module BaseTypes where


  module Unit where
   data ⊤ : Set where
    unit : ⊤


  module Bool where
   data Bool : Set where
    true : Bool
    false : Bool

   module Operations where
    open Equality.Definition
    if_then_else_ : ∀ {i} {A : Set i} → Bool → A → A → A
    if true then a else b = a
    if false then a else b = b

    -- this is definitely not an implementation of if then else
    -- but it still type-checks just fine
    bad-ite : ∀ {i} {A : Set i} → Bool → A → A → A
    bad-ite true a b = a
    bad-ite false a b = a

    -- so our type-signature must not quite be capturing what it means to be if_then_else
    -- let's try this instead:

    dif_then_else_ : ∀ {i} {P : Bool → Set i} → (b : Bool) → P true → P false → P b
    dif true then Ptrue else Pfalse = Ptrue
    dif false then Ptrue else Pfalse = Pfalse

    dite₂ : ∀ {i} {P : Bool → Set i} → (b : Bool) → ((b ≡ true) → P true) → ((b ≡ false) → P false) → P b
    dite₂ true t f = t refl
    dite₂ false t f = f refl

  module Nat where
   data Nat : Set where
    zero : Nat
    suc : Nat → Nat

   {-# BUILTIN NATURAL Nat #-}

  module Fin where
   open Nat renaming (Nat to ℕ)
   module Definition where
    data Fin : ℕ → Set where
     zero : {n : ℕ} → Fin (suc n)
     suc : {n : ℕ} → Fin n → Fin (suc n)
   open Definition public
   module Operations where
    ℕ[_] : {n : ℕ} → Fin n → ℕ
    ℕ[ zero ] = zero
    ℕ[ suc x ] = suc (ℕ[ x ])

    n→Fin[1+n] : (n : ℕ) → Fin (suc n)
    n→Fin[1+n] 0 = zero
    n→Fin[1+n] (suc n) = suc (n→Fin[1+n] n)

    FinLift : {n : ℕ} → Fin n → Fin (suc n)
    FinLift {0} ()
    FinLift {suc n} zero = zero
    FinLift {suc n} (suc {n} m) = suc (FinLift {n} m)

    zero₂ : Fin 2
    zero₂ = zero {1}

    one₂ : Fin 2
    one₂ = suc {1} (zero {0})

    _-_ : (n : ℕ) → (m : Fin (suc n)) → Fin (suc n)
    0 - zero = zero
    0 - (suc ())
    (suc x) - zero = n→Fin[1+n] (suc x)
    (suc x) - (suc y) = FinLift (x - y)
   open Operations
   module Properties where
    open Equality.Definition
    open Equality.Properties
    ℕ[n→Fin[1+n]]=n : (n : ℕ) → ℕ[ n→Fin[1+n] n ] ≡ n
    ℕ[n→Fin[1+n]]=n 0 = refl
    ℕ[n→Fin[1+n]]=n (suc n) = proof
     where
      proof = cong suc (ℕ[n→Fin[1+n]]=n n)
    
    ℕ[n-0]=n : (n : ℕ) → (ℕ[ (n - zero) ]) ≡ n
    ℕ[n-0]=n 0 = refl
    ℕ[n-0]=n (suc n) = proof
     where
      lemma1 : ℕ[ (suc n) - zero ] ≡ ℕ[ n→Fin[1+n] (suc n) ]
      lemma1 = refl

      lemma2 : ℕ[ n→Fin[1+n] (suc n) ] ≡ ℕ[ suc (n→Fin[1+n] n) ]
      lemma2 = refl

      lemma3 : ℕ[ suc (n→Fin[1+n] n) ] ≡ suc (ℕ[ n→Fin[1+n] n ])
      lemma3 = refl

      proof = cong suc (ℕ[n→Fin[1+n]]=n n)
    {-
    ℕ[n-0]=n (suc (suc n)) = proof
     where
      lemma1 : ℕ[ (suc (suc n)) - zero ] ≡ ℕ[ n→Fin[1+n] (suc (suc n)) ]
      lemma1 = refl

      lemma2 : ℕ[ n→Fin[1+n] (suc (suc n)) ] ≡ ℕ[ suc (n→Fin[1+n] (suc n)) ]
      lemma2 = refl

      lemma3 : ℕ[ suc (n→Fin[1+n] (suc n)) ] ≡ suc (ℕ[ n→Fin[1+n] (suc n)])
      lemma3 = refl

      lemma4 : ℕ[ n→Fin[1+n] (suc n)] ≡ (suc n)
      lemma4 = ℕ[n→Fin[1+n]]=n (suc n)
-}
      {-
      lemma4 : ℕ[ ((suc n) - zero) ] ≡ ℕ[ n→Fin[1+n] (suc n) ]
      lemma4 = refl

      lemma5 : ℕ[ (n - zero) ] ≡ n
      lemma5 = ℕ[n-0]=n n
      -}

      {-
      fails termination check!?
      lemma6 : ℕ[ ((suc n) - zero) ] ≡ (suc n)
      lemma6 = ℕ[n-0]=n (suc n)
      -}
{-
      lemma6 : ℕ[ n→Fin[1+n] (suc n) ] ≡ suc ℕ[ n→Fin[1+n] n ]
      lemma6 = refl

      
      lemma7 : ℕ[ n→Fin[1+n] n ] ≡ n
      lemma7 =  ℕ[n→Fin[1+n]]=n n

      lemma8 : 

      proof -- = cong suc lemma6
-}
    -- ℕ[n-n]=0 : (n : ℕ) → (ℕ[ (n - (n→Fin[1+n] n)) ]) ≡ 0
  module List where
   data List {i} (A : Set i) : Set i where
    [] : List A
    _∷_ : A → List A → List A

   infixr 0 _∷_
   module Operations where
    open Bool
    open Bool.Operations
    foldr : ∀ {i j} {A : Set i} {B : Set j} → (A → B → B) → B → List A → B
    foldr f b [] = b
    foldr f b (a ∷ as) = f a (foldr f b as)

    map : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → List A → List B
    map f [] = []
    map f (a ∷ as) = (f a) ∷ (map f as)

    _++_ : ∀ {i} {A : Set i} → (x y : List A) → List A
    [] ++ ys = ys
    (x  ∷ xs) ++ ys = x ∷ (xs ++ ys)

    rev : ∀ {i} {A : Set i} → List A → List A
    rev [] = []
    rev (x ∷ xs) = (rev xs) ++ (x ∷ [])

    find  : ∀ {i} {A : Set i} → A → List A → (A → A → Bool) → Bool
    find x [] f = false
    find x (y ∷ ys) f = if (f x y) then true else (find x ys f)
   open Operations public
   module Predicates where
   {-
    _∈_ : ∀ {i} {A : Set i} → A → List A → Set i
    x ∈ L = 
  -}
  module Vector where
   open List
   open Nat renaming (Nat to ℕ)
   data Vector {i} (A : Set i) : ℕ → Set i where
    [] : Vector A 0
    _∷_ : {n : ℕ} → A → Vector A n → Vector A (suc n)

   toList : ∀ {i} {A : Set i} {n : ℕ} → Vector A n → List A
   toList [] = []
   toList (a ∷ as) = a ∷ (toList as)

  module Tree where
   open List
   data Tree {i} (A : Set i) : Set i where
    leaf : A → Tree A
    node : List (Tree A) → Tree A

  module VTree where
   open Vector
   open Nat renaming (Nat to ℕ)
   data VTree {i} (A : Set i) (n : ℕ) : Set i where
    leaf : A → VTree A n
    node : Vector (VTree A n) n → VTree A n

  module VTree' where
   open Tree
   open Vector
   open Nat renaming (Nat to ℕ)
   data VTree' {i} (A : Set i) (n : ℕ) : Set i where
    node : Vector (Tree A) n → VTree' A n

 open Product public
 open Biimplication.Definition public
 open Negation.Definition public
 open Sum public
 open BaseTypes public

module BaseResults where
 open BaseDefinitions
 not-exists↔forall-not : ∀ {i j} {A : Set i} {P : A → Set j} → ((¬ (∃ x ∈ A , P x)) ↔ ((x : A) → ¬ (P x)))
 not-exists↔forall-not {i} {j} {A} {P} = (proof-left , proof-right)
  where
   proof-left : (¬ (∃ x ∈ A , P x)) → ((x : A) → ¬ (P x))
   proof-left ¬∃x,Px x Px = ¬∃x,Px (x , Px)
  
   proof-right : ((x : A) → ¬ (P x)) → (¬ (∃ x ∈ A , P x))
   proof-right ∀x,¬Px ∃x,Px = ∀x,¬Px (proj1 ∃x,Px) (proj2 ∃x,Px)

 -- lose information
 [¬A∨¬B]→¬[A∧B] : ∀ {i j} {A : Set i} {B : Set j} → ((¬ A) ∨ (¬ B)) → (¬ (A ∧ B))
 [¬A∨¬B]→¬[A∧B] {i} {j} {A} {B} = proof
  where
   proof : ((¬ A) ∨ (¬ B)) → ¬ (A ∧ B)
   proof (inl ¬A) (a , b) = ¬A a
   proof (inr ¬B) (a , b) = ¬B b


 -- can't do it:
 -- ¬[A∧B]→[¬A∨¬B]

 {-
 ¬[A∧B]→¬[A∨B] : ∀ {i j} {A : Set i} {B : Set j} → (¬ (A ∧ B)) → (¬ (A ∨ B))
 ¬[A∧B]→¬[A∨B] {i} {j} {A} {B} f (inl a)
 -}

 [¬A∨B]→[A→B] : ∀ {i j} {A : Set i} {B : Set j} → ((¬ A) ∨ B) → A → B
 [¬A∨B]→[A→B] (inl ¬A) a = ω (¬A a)
 [¬A∨B]→[A→B] (inr b) a = b

 ¬[A∨B]→[¬A∧¬B] : ∀ {i j} {A : Set i} {B : Set j} → (¬ (A ∨ B)) → ((¬ A) ∧ (¬ B))
 ¬[A∨B]→[¬A∧¬B] {i} {j} {A} {B} f = (proof-left , proof-right)
  where
   proof-left : ¬ A
   proof-left a = f (inl a)

   proof-right : ¬ B
   proof-right b = f (inr b)

 [¬A∧¬B]→¬[A∨B] : ∀ {i j} {A : Set i} {B : Set j} → ((¬ A) ∧ (¬ B)) → (¬ (A ∨ B))
 [¬A∧¬B]→¬[A∨B] (¬A , ¬B) (inl a) = ¬A a
 [¬A∧¬B]→¬[A∨B] (¬A , ¬B) (inr b) = ¬B b


 ¬[A→¬¬B]→¬[A→B] : ∀ {i j} {A : Set i} {B : Set j} → ¬ (A → ¬ (¬ B)) → ¬ (A → B)
 ¬[A→¬¬B]→¬[A→B] {i} {j} {A} {B} f g = proof
  where
   lemma1 : (A → B) → (A → ¬ (¬ B))
   lemma1 h a ¬B = ¬B (h a)   

   proof = f (lemma1 g)


 ∀-lemma : ∀ {i j} {A : Set i} (P : A → Set j) → A → ((x : A) → ¬ (P x)) → ¬ ((x : A) → (P x))
 ∀-lemma {i} {j} {A} P x f f' = (f x) (f' x) 

 ∀-lemma2 : ∀ {i j} {A : Set i} (P : A → Set j) → ¬ A → ((x : A) → P x) ∧ ((x : A) → ¬ (P x))
 ∀-lemma2 {i} {j} {A} P ¬A = (proof-left , proof-right)
  where
   proof-left : (x : A) → P x
   proof-left x = ω (¬A x)
  
   proof-right : (x : A) → ¬ (P x)
   proof-right x = ω (¬A x)

module Boolean where
 module Operations where
  
  open BaseDefinitions.BaseTypes.Bool
  not : Bool → Bool
  not true = false
  not false = true
  
  _and_ : Bool → Bool → Bool
  true and x = x
  false and x = false

  _or_ : Bool → Bool → Bool
  true or x = true
  false or x = x

  _eq_ : Bool → Bool → Bool
  true eq true = true
  true eq false = false
  false eq true = false
  false eq false = true


module Containers where
-- Pairs
-- Unions
-- Sets
-- Multisets / Bags
-- Lists
-- Vectors
-- Streams
-- Trees
-- Maybes
-- Coq.FSet
-- Coq.MSet
-- Coq.Lists.ListSet
 data Maybe {i} (A : Set i) : Set i where
  Nothing : Maybe A
  Just : A → Maybe A


module Functions where
 open BaseDefinitions.Implication
 module Special where
  id : ∀ {i} {A : Set i} → A → A
  id = λ x → x
















 module Composition where
  module Definition where
   _∘_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (B → C) → (A → B) → (A → C)
   g ∘ f = λ x → g (f x)

  open Definition

  
  module Properties where
   open BaseDefinitions.Equality.Definition
   ∘-assoc :
    ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
    → (f : A → B) → (g : B → C) → (h : C → D)
    → ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
   ∘-assoc f g h = refl
 open Composition.Definition
 module Iteration where
  open Composition.Definition
  open BaseDefinitions.Nat
  module Definition where
   _**_ : ∀ {i} {A : Set i} → (A → A) → Nat → (A → A)
   f ** zero = λ x → x
   f ** (suc n) = f ∘ (f ** n)

  open Definition
  
 open Iteration
 module GenericProperties where
  open BaseDefinitions.Equality.Definition
  open BaseDefinitions.Relations.BinaryRelations.Properties.Reflexivity
  {- Associativity:
     Associativity only defined on binary operators:
     f : A → B → C
     f (f x y) z ≡ f x (f y z)
     x : D
     y : E
     z : F
     
     (f x y) → A = D, B = E
     f : A → B → C
     x : A
     y : B
     z : F
     f (f x y) z → A = C, F = C
     f : A → B → A
     x : A
     y : B
     z : A
     (f y z) → A = B, A = A
     f : A → A → A
 -}
  →-refl : ∀ {i} {A : Set i} → A → A
  →-refl = λ x → x
  {-
  →-refl : ∀ {i j} → Reflexive {lsuc i} {j} (Set i) _⊃_
  →-refl A = λ x → x
  -}

  →-trans : ∀ {i} {A B C : Set i} → (A → B) → (B → C) → (A → C)
  →-trans = λ f g x → g (f x)

 module Predicates where
  open Special
  open Composition.Definition
  open BaseDefinitions.Product
  open BaseDefinitions.Equality.Definition
  Associative : ∀ {i} {A : Set i} (f : A → A → A) → Set i
  Associative {i} {A} f = (x y z : A) → (f (f x y) z) ≡ (f x (f y z))

  _isAssociative : ∀ {i} {A : Set i} (f : A → A → A) → Set i
  _isAssociative = Associative

  Commutative : ∀ {i} {A : Set i} (f : A → A → A) → Set i
  Commutative {i} {A} f = (x y : A) → (f x y) ≡ (f y x)

  _isCommutative : ∀ {i} {A : Set i} (f : A → A → A) → Set i
  _isCommutative = Commutative

  Idempotent : ∀ {i} {A : Set i} (f : A → A → A) → Set i
  Idempotent {i} {A} f = (x : A) → (f x x) ≡ x

  _isIdempotent : ∀ {i} {A : Set i} (f : A → A → A) → Set i
  _isIdempotent = Idempotent

  Injective : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  Injective {i} {j} {A} {B} f = {x y : A} → (f x) ≡ (f y) → x ≡ y

  _isInjection : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  _isInjection = Injective

  _isInjective : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  _isInjective = Injective

  Surjective : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  Surjective {i} {j} {A} {B} f = (y : B) → ∃ x ∈ A , (f x ≡ y)

  _isSurjection : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  _isSurjection = Surjective

  _isSurjective : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  _isSurjective = Surjective

  Bijective : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  Bijective f = (f isInjective) ∧ (f isSurjective)

  _isBijection : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  _isBijection = Bijective

  _isBijective : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  _isBijective = Bijective

 module Identities where
  open BaseDefinitions.Product
  open BaseDefinitions.Equality.Definition
  _isLIdentityFor_wrt_ : ∀ {i} {A : Set i} (x y : A) → (f : A → A → A) → Set i
  y isLIdentityFor x wrt f = (f y x) ≡ x

  _isRIdentityFor_wrt_ : ∀ {i} {A : Set i} (x y : A) → (f : A → A → A) → Set i
  y isRIdentityFor x wrt f = (f x y) ≡ x

  _isIdentityFor_wrt_ : ∀ {i} {A : Set i} (x y : A) → (f : A → A → A) → Set i
  y isIdentityFor x wrt f = (y isLIdentityFor x wrt f) ∧ (y isRIdentityFor x wrt f)

  _isLIdentityWrt_ : ∀ {i} {A : Set i} (x : A) → (f : A → A → A) → Set i
  _isLIdentityWrt_ {i} {A} e f = (x : A) → (e isLIdentityFor x wrt f)

  _isRIdentityWrt_ : ∀ {i} {A : Set i} (x : A) → (f : A → A → A) → Set i
  _isRIdentityWrt_ {i} {A} e f = (x : A) → (e isRIdentityFor x wrt f)

  -- is one of these versions preferable?

  -- v1: probably this one:
  _isIdentityWrt_ : ∀ {i} {A : Set i} (x : A) → (f : A → A → A) → Set i
  _isIdentityWrt_ {i} {A} e f = (e isLIdentityWrt f) ∧ (e isRIdentityWrt f)

  -- v2
  _isIdentityWrt₂_ : ∀ {i} {A : Set i} (x : A) → (f : A → A → A) → Set i
  _isIdentityWrt₂_ {i} {A} e f = (x : A) → (e isIdentityFor x wrt f)

  _hasLIdentity : ∀ {i} {A : Set i} (f : A → A → A) → Set i
  _hasLIdentity {i} {A} f = ∃ e ∈ A , (e isLIdentityWrt f)

  _hasRIdentity : ∀ {i} {A : Set i} (f : A → A → A) → Set i
  _hasRIdentity {i} {A} f = ∃ e ∈ A , (e isRIdentityWrt f)

  _hasIdentity : ∀ {i} {A : Set i} (f : A → A → A) → Set i
  _hasIdentity {i} {A} f = ∃ e ∈ A , (e isIdentityWrt f)
  

 module Inverses where
  module FunctionInverses where
   open Special
   open BaseDefinitions.Product
   open BaseDefinitions.Equality.Definition
   _isLInverseOfᵢ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set i
   g isLInverseOfᵢ f = (g ∘ f) ≡ id

   _isRInverseOfᵢ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set j
   g isRInverseOfᵢ f = (f ∘ g) ≡ id
   
   _isInverseOfᵢ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set (i ⊔ j)
   g isInverseOfᵢ f = (g isLInverseOfᵢ f) ∧ (g isRInverseOfᵢ f)  

   _isLInverseOfₑ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set i
   _isLInverseOfₑ_ {i} {j} {A} {B} g f = (x : A) → (g (f x)) ≡ x

   _isRInverseOfₑ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set j
   _isRInverseOfₑ_ {i} {j} {A} {B} g f = (x : B) → (f (g x)) ≡ x

   _isInverseOfₑ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set (i ⊔ j)
   g isInverseOfₑ f = (g isLInverseOfₑ f) ∧ (g isRInverseOfₑ f)

   _isInverseOfᵢᵢ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set (i ⊔ j)
   _isInverseOfᵢᵢ_ = _isInverseOfᵢ_

   _isInverseOfₑₑ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set (i ⊔ j)
   _isInverseOfₑₑ_ = _isInverseOfₑ_
   

   _isInverseOfᵢₑ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set (i ⊔ j)
   g isInverseOfᵢₑ f = (g isLInverseOfᵢ f) ∧ (g isRInverseOfₑ f)

   _isInverseOfₑᵢ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set (i ⊔ j)
   g isInverseOfₑᵢ f = (g isLInverseOfₑ f) ∧ (g isRInverseOfᵢ f)
  


   -- has inverse unary predicate

   _hasLInverseᵢ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
   _hasLInverseᵢ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , (g isLInverseOfᵢ f)

   _hasRInverseᵢ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
   _hasRInverseᵢ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , (g isRInverseOfᵢ f)

   _hasInverseᵢ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
   _hasInverseᵢ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , (g isInverseOfᵢ f)

   _hasLInverseₑ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
   _hasLInverseₑ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , (g isLInverseOfₑ f)

   _hasRInverseₑ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
   _hasRInverseₑ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , (g isRInverseOfₑ f)

   _hasInverseₑ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
   _hasInverseₑ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , (g isInverseOfₑ f)

   _hasInverseᵢᵢ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
   _hasInverseᵢᵢ = _hasInverseᵢ

   _hasInverseₑₑ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
   _hasInverseₑₑ = _hasInverseₑ

   _hasInverseᵢₑ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
   _hasInverseᵢₑ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , (g isInverseOfᵢₑ f)

   _hasInverseₑᵢ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
   _hasInverseₑᵢ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , (g isInverseOfₑᵢ f)

  {-
   relativized to some equivalence relation?

  -}


  open FunctionInverses
  module ObjectInverses where
   -- not meaningful to talk about true "inverses" without an identity element already known
   -- identity is more basic than inverse.
   -- object inverses more basic than function inverses or function inverses more basic than object inverses or neither?
   -- functions generalize the situation; morphisms between objects
   -- translation of abstract algebra into category theory: objects become morphisms, some operation becomes composition of morphisms
   
   {-
   _isRInverseOfₒ_wrt_ : ∀ {i} {A : Set i} (y x : A) → (A → A → A) → Set i
   -}


 open Inverses
      
 








module BaseArithmetic where
 open BaseDefinitions.BaseTypes.Nat public renaming (Nat to ℕ)
 module Operations where
  _+_ : ℕ → ℕ → ℕ
  0 + y = y
  (suc x) + y = suc (x + y)

  _*_ : ℕ → ℕ → ℕ
  0 * y = 0
  (suc x) * y = y + (x * y)

  _^_ : ℕ → ℕ → ℕ
  x ^ 0 = 1
  x ^ (suc y) = y * (x ^ y)

  pred : ℕ → ℕ
  pred 0 = 0
  pred (suc x) = x

  _-_ : ℕ → ℕ → ℕ
  0 - x = 0
  (suc x) - 0 = (suc x)
  (suc x) - (suc y) = x - y

  {-
  mod : ℕ → ℕ → ℕ
  mod 
  div : ℕ → ℕ → ℕ
  -}
 open Operations public
 module BooleanPredicates where
  open BaseDefinitions.BaseTypes.Bool
  _eq_ : ℕ → ℕ → Bool
  0 eq 0 = true
  0 eq (suc y) = false
  (suc x) eq 0 = false
  (suc x) eq (suc y) = x eq y

  _lte_ : ℕ → ℕ → Bool
  0 lte x = true
  (suc x) lte 0 = false
  (suc x) lte (suc y) = x lte y

  _lt_ : ℕ → ℕ → Bool
  0 lt 0 = false
  0 lt (suc y) = true
  (suc x) lt 0 = false
  (suc x) lt (suc y) = x lt y

  _gte_ : ℕ → ℕ → Bool
  x gte 0 = true
  0 gte (suc y) = false
  (suc x) gte (suc y) = x gte y

  _gt_ : ℕ → ℕ → Bool
  0 gt 0 = false
  (suc x) gt 0 = true
  0 gt (suc y) = false
  (suc x) gt (suc y) = x gt y
 open BooleanPredicates
 module Relations where
  open BaseDefinitions.Equality.Definition
  open BaseDefinitions.Product
  open BaseDefinitions.Negation.Definition
  {-
  _~_ : ℕ → ℕ → Set
  _~_ = _≡_ {A = ℕ}
  -}

  _≤_ : ℕ → ℕ → Set
  x ≤ y = ∃ k ∈ ℕ , ((x + k) ≡ y)

  _≰_ : ℕ → ℕ → Set
  x ≰ y = ¬ (x ≤ y)

  _<_ : ℕ → ℕ → Set
  x < y = ∃ k ∈ ℕ , ((x + (suc k)) ≡ y)

  _≮_ : ℕ → ℕ → Set
  x ≮ y = ¬ (x < y)

  _≥_ : ℕ → ℕ → Set
  x ≥ y = y ≤ x

  _≱_ : ℕ → ℕ → Set
  x ≱ y = ¬ (x ≥ y)

  _>_ : ℕ → ℕ → Set
  x > y = y < x

  _≯_ : ℕ → ℕ → Set
  x ≯ y = ¬ (x > y)

  _divides_ : ℕ → ℕ → Set
  a divides b = ∃ k ∈ ℕ , ((a * k) ≡ b)

  log-base_[_]=_ : ℕ → ℕ → ℕ → Set
  log-base k [ x ]= n = (k ^ n) ≡ x

  _logs_ : ℕ → ℕ → Set
  a logs b = ∃ k ∈ ℕ , ((a ^ k) ≡ b)
  

 open Relations
 module Results where
  






module BaseAbstractAlgebra where
 open Functions
 -- to bundle or not to bundle?
 -- bundled:
 {-
 record Monoid {i} : Set (lsuc i) where
  field
   M : Set i
   _∘_ : M → M → M
   
 -- unbundled:
 record monoid {i} (M : Set i) (_∘_ : M → M → M) : Set i where
  field
   identity : _∘_ hasIdentity
   associativity : _∘_ isAssociative
 record Group {i} : Set (lsuc i) where
  field
   carrier : Set i
 -}
   
module FunctionArithmetic where
 open BaseDefinitions.Equality.Definition
 open BaseDefinitions.Equality.Properties
 open BaseArithmetic
 open Functions
 open Functions.Special
 open Functions.Composition.Definition
 open Functions.Composition.Properties
 open Functions.Iteration.Definition
 module ExponentialLaws where

  *-id : ∀ {i} {A : Set i} (f : A → A) → ((f ** 0) ≡ id)
  *-id f = refl

  idⁿ=id : ∀ {i} {A : Set i} → (n : ℕ) → (id {i} {A} ** n) ≡ id
  idⁿ=id 0 = refl
  idⁿ=id (suc n) = idⁿ=id n

  +-law : ∀ {i} {A : Set i} (f : A → A) → (n m : ℕ) → ((f ** n) ∘ (f ** m)) ≡ (f ** (n + m))
  +-law f 0 m = refl
  +-law f (suc n) m = proof
   where
    lemma1 : ((f ** (suc n)) ∘ (f ** m)) ≡ ((f ∘ (f ** n)) ∘ (f ** m))
    lemma1 = refl

    lemma2 : ((f ∘ (f ** n)) ∘ (f ** m)) ≡ (f ∘ ((f ** n) ∘ (f ** m)))
    lemma2 = ∘-assoc (f ** m) (f ** n) f

    lemma3 : ((f ** n) ∘ (f ** m)) ≡ (f ** (n + m))
    lemma3 = +-law f n m

    lemma4 : (f ∘ ((f ** n) ∘ (f ** m))) ≡ (f ∘ (f ** (n + m)))
    lemma4 = cong (_∘_ f) lemma3

    lemma5 : (f ∘ (f ** (n + m))) ≡ (f ** (suc (n + m)))
    lemma5 = refl

    lemma6 : (f ** (suc (n + m))) ≡ (f ** ((suc n) + m))
    lemma6 = refl

    proof = ≡-trans lemma2 lemma4
  {-
  *-law : ∀ {i} {A : Set i} (f : A → A) → (m n : ℕ) → ((f ** m) ** n) ≡ (f ** (m * n))
  *-law f 0 n = refl
  *-law f (suc m) n = proof
   where
    proof
  -}



module Orders where
 -- probably belongs with equivalence relations and "Relations" more generally, i.e.
 -- Order subtypes relation
 open BaseDefinitions.Negation.Definition
 open BaseDefinitions.Sum
 open BaseDefinitions.Product
 open BaseDefinitions.Relations
 open BaseDefinitions.Relations.Properties.Reflexivity
 open BaseDefinitions.Relations.Properties.Symmetry
 open BaseDefinitions.Relations.Properties.Antisymmetry
 open BaseDefinitions.Relations.Properties.Transitivity
 open BaseDefinitions.Equality.Definition
 open BaseDefinitions.Equality.Properties
 -- algebraic structures; to bundle or not to bundle
 record PartialOrder {i j} {A : Set i} (R : A → A → Set j) : Set (i ⊔ j) where
  field
   reflexive : Reflexive R
   transitive : Transitive R
   antisymmetric : Antisymmetric {i} {j} {i} {A} _≡_ ≡-equiv R 

 record PartialOrder₂ {i j k} : Set ((lsuc i) ⊔ ((lsuc j) ⊔ (lsuc k))) where
  field
   S : Set i
   _≤_ : S → S → Set j 
   _~_ : S → S → Set k
   ~-equiv : Equivalence _~_
   reflexive : Reflexive _≤_
   transitive : Transitive _≤_
   antisymmetric : Antisymmetric _~_ ~-equiv _≤_

 record PartialOrder₃ {i j k} {A : Set i} (_~_ : A → A → Set k) (R : A → A → Set j) : Set (i ⊔ (j ⊔ k)) where
  field
   ~-equiv : Equivalence _~_
   reflexive : Reflexive R
   transitive : Transitive R
   antisymmetric : Antisymmetric {i} {j} {k} {A} _~_ ~-equiv R

 record PartialOrder₄ {i j k} {A : Set i} (_~_ : A → A → Set k) (~-equiv : Equivalence _~_) (R : A → A → Set j) : Set (i ⊔ (j ⊔ k)) where
  field
   reflexive : Reflexive R
   transitive : Transitive R
   antisymmetric : Antisymmetric {i} {j} {k} {A} _~_ ~-equiv R
  

 record TotalOrder {i j} {A : Set i} (R : A → A → Set j) : Set (i ⊔ j) where
  field
   antisymmetric : Antisymmetric {i} {j} {i} {A} _≡_ ≡-equiv R 
   transitive : Transitive R
   total : (x y : A) → R x y ∨ R y x

 record TotalOrder₂ {i j k} : Set ((lsuc i) ⊔ ((lsuc j) ⊔ (lsuc k))) where
  field
   S : Set i
   _≤_ : S → S → Set j 
   _~_ : S → S → Set k
   ~-equiv : Equivalence _~_
   antisymmetric : Antisymmetric _~_ ~-equiv _≤_
   transitive : Transitive _≤_
   total : (x y : S) → (x ≤ y) ∨ (y ≤ x)
 
 record TotalOrder₃ {i j k} {A : Set i} (_~_ : A → A → Set k) (R : A → A → Set j) : Set (i ⊔ (j ⊔ k)) where
  field
   ~-equiv : Equivalence _~_
   antisymmetric : Antisymmetric {i} {j} {k} {A} _~_ ~-equiv R
   transitive : Transitive R
   total : (x y : A) → R x y ∨ R y x
   
 
 record TotalOrder₄ {i j k} {A : Set i} (_~_ : A → A → Set k) (~-equiv : Equivalence _~_) (R : A → A → Set j) : Set (i ⊔ (j ⊔ k)) where
  field
   antisymmetric : Antisymmetric {i} {j} {k} {A} _~_ ~-equiv R
   transitive : Transitive R
   total : (x y : A) → R x y ∨ R y x

 MakeStrict : ∀ {i j} {A : Set i} (R : A → A → Set j) → (A → A → Set (i ⊔ j))
 MakeStrict R x y = (R x y) ∧ (¬ (x ≡ y))

 MakeStrict~ : ∀ {i j k} {A : Set i} (_~_ : A → A → Set j) → (R : A → A → Set k) → (A → A → Set (j ⊔ k))
 MakeStrict~ _~_ R x y = (R x y) ∧ (¬ (x ~ y))
 

module MetricSpaces where
 open BaseDefinitions.Equality.Definition
 open BaseDefinitions.Relations
-- can you define it without reference to the reals?
 open Orders
 record MetricSpace {i j} : Set ((lsuc i) ⊔ (lsuc j)) where
  field
   I : Set i
   _≤_ : I → I → Set j
   ≤-totalOrder : TotalOrder _≤_
   z : I
   z-bottom : (i : I) → z ≤ i
   _+_ : I → I → I
   M : Set j
   d : M → M → I   
   non-negativity : (x y : M) → z ≤ (d x y)
   identity : {x y : M} → (d x y) ≡ z → x ≡ y
   commutativity : (x y : M) → (d x y) ≡ (d y x)
   triangle≠ : (x y z : M) → (d x z) ≤ ((d x y) + (d y z))
      

 record MetricSpace₂ {i} {j} {k} {l} {m} : Set (((((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) ⊔ (lsuc l)) ⊔ (lsuc m)) where
  field
   I : Set i
   _~_ : I → I → Set j
   ~-equiv : Equivalence _~_
   _≤_ : I → I → Set k
   ≤-totalOrder : TotalOrder₄ _~_ ~-equiv _≤_
   _+_ : I → I → I
   z : I
   z-bottom : (i : I) → z ≤ i
   M : Set l
   _≈_ : M → M → Set m
   ≈-equiv : Equivalence _≈_
   d : M → M → I
   non-negativity : (x y : M) → z ≤ (d x y)
   identity : {x y : M} → (d x y) ~ z → x ≈ y
   commutativity : (x y : M) → (d x y) ~ (d y x)
   triangle≠ : (x y z : M) → (d x z) ≤ ((d x y) + (d y z))


      
module Limits where
 open BaseDefinitions.Product
 open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
 open BaseArithmetic.Relations hiding (_<_)
 open Orders
 open MetricSpaces
-- epsilon-delta convergence
 
 εδ-convergent-sequence :
  ∀{i j k l m}
  (M' : MetricSpace₂ {i} {j} {k} {l} {m}) →
   let M = (MetricSpace₂.M M') in
    (S : ℕ → M) → Set (i ⊔ (j ⊔ (k ⊔ l)))
  
 εδ-convergent-sequence {i} {j} {k} {l} {m} M' S = 
   let I = (MetricSpace₂.I M') in
   let d = (MetricSpace₂.d M') in
   let z = (MetricSpace₂.z M') in
   let M = (MetricSpace₂.M M') in
   let _<_ = (MakeStrict~ (MetricSpace₂._~_ M') (MetricSpace₂._≤_ M')) in
    (S : ℕ → M) →
    (ε : I) →
    (z < ε) →
    (∃ δ ∈ ℕ , ((n : ℕ) → (n > δ) → ((d (S n) (S (suc n))) < ε)))

module Decidability where
 open BaseDefinitions.Void
 open BaseDefinitions.BaseTypes.Unit
 open BaseDefinitions.Negation.Definition
 open BaseDefinitions.BaseTypes.Bool
 data Dec {i} (P : Set i) : Set i where
  yes : (p : P) → Dec P
  no : (¬p : ¬ P) → Dec P

 ⌋_⌊ : ∀ {i} {A : Set i} → Dec A → Bool
 ⌋ yes _ ⌊ = true
 ⌋ no  _ ⌊ = false

 T : Bool → Set
 T true = ⊤
 T false = ⊥

 True : ∀ {i} {A : Set i} → Dec A → Set
 True (yes _) = ⊤
 True (no _) = ⊥

 False : ∀ {i} {A : Set i} → Dec A → Set
 False (yes _) = ⊥
 False (no _) = ⊤

module Numbers where
 open BaseDefinitions.Void
 open BaseDefinitions.BaseTypes.Unit
 open BaseDefinitions.BaseTypes.Bool
 open BaseDefinitions.BaseTypes.Bool.Operations
 open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
 open BaseDefinitions.BaseTypes.Fin
 open BaseDefinitions.Product
 open BaseDefinitions.Equality.Definition
 open BaseDefinitions.Equality.Properties
 open BaseArithmetic.Operations
 open BaseArithmetic.BooleanPredicates
 open Decidability

 eq-decides-≡ : {x y : ℕ} → ((x eq y) ≡ true) → (x ≡ y)
 eq-decides-≡ {0} {0} refl = refl
 eq-decides-≡ {0} {(suc y)} ()
 eq-decides-≡ {(suc x)} {0} ()
 eq-decides-≡ {(suc x)} {(suc y)} p = proof
  where
   lemma1 : ((suc x) eq (suc y)) ≡ true
   lemma1 = p

   lemma2 : ((suc x) eq (suc y)) ≡ (x eq y)
   lemma2 = refl

   lemma3 : (x eq y) ≡ true
   lemma3 = p

   lemma4 : x ≡ y
   lemma4 = eq-decides-≡ lemma3

   proof = cong suc lemma4

 
 eq-decides-≡₂ : {x y : ℕ} → (x ≡ y) → ((x eq y) ≡ true)
 eq-decides-≡₂ {0} {0} refl = refl
 eq-decides-≡₂ {(suc x)} {0} ()
 eq-decides-≡₂ {0} {(suc y)} ()
 eq-decides-≡₂ {(suc x)} {(suc y)} p = proof
  where
   lemma1 : (suc x) ≡ (suc y)
   lemma1 = p

   lemma2 : x ≡ y
   lemma2 = cong pred lemma1

   lemma3 : (x eq y) ≡ true
   lemma3 = eq-decides-≡₂ lemma2

   lemma4 : ((suc x) eq (suc y)) ≡ (x eq y)
   lemma4 = refl

   proof = lemma3

 true≠false : true ≠ false
 true≠false ()

 
 _≟_ : (x y : ℕ) → Dec (x ≡ y)
 x ≟ y = dite₂ {lzero} {λ b → (Dec (x ≡ y))} (x eq y) true-case false-case
  where
   true-case : ((x eq y) ≡ true) → Dec (x ≡ y)
   true-case p = yes (eq-decides-≡ p)

   false-case : ((x eq y) ≡ false) → Dec (x ≡ y)
   false-case p = proof
    where
     lemma1 : (x eq y) ≡ false
     lemma1 = p

     lemma2 : (x eq y) ≠ true
     lemma2 g = true≠false (≡-trans (≡-sym g) lemma1)

     lemma3 : x ≠ y
     lemma3 h = lemma2 (eq-decides-≡₂ h)

     proof = no lemma3


 module Naturals where
  module PowerExpansion where
   open BaseDefinitions.BaseTypes.List
   Nat : Set
   Nat = List Bool
   -- problematic:
   -- what is [] ? 0 would be a natural choice but it would be even more natural if it wasn't even there
   -- non-unique representation due to leading 0's.
   -- can we create a representation that gets rid of [] and the trailing 0's but doesn't change the
   -- representation from positional notation?
   -- *non-empty* list of items with leading item not equal to 0.
   
  -- naturals as the free commutative monoid on 1 generator?
  -- equivalent to free monoid on 1 generator?
  -- free objects unique?
 module NonZeroNats where
  -- the NonZeroNats have the same "structure"
  -- but different operations
  -- can define them as a subset of Nat
  ℕ*₁ : ℕ → Set
  ℕ*₁ 0 = ⊥
  ℕ*₁ (suc n) = ⊤
    -- but then it carries around this "proof of subsetness" info with it
    -- (n : ℕ) → ℕ*₁ n → ...

  ℕ*₂ : Set
  ℕ*₂ = ∃ x ∈ ℕ , (ℕ*₁ x)

  {-
   -- maybe with propositional truncation:
  ℕ*₃ : Set
  ℕ*₃ = ∃ x ∈ ℕ , | (ℕ*₁ x) |

  But we still want to be able to treat it directly as an object of type ℕ
  -}


  -- On the other extreme:
  -- can define it as a new type
  data ℕ* : Set where
   one : ℕ*
   suc : ℕ* → ℕ*

  -- but still have to map it into ℕ like:
  ℕ*→ℕ : ℕ* → ℕ
  ℕ*→ℕ one = 1
  ℕ*→ℕ (suc n*) = suc (ℕ*→ℕ n*)

  -- and then one might ask, why didn't we define ℕ in terms of ℕ* ?
   -- ℕ* is seen as a subset of ℕ
   -- but there are situations where it occurs independently of ℕ
   -- multiplication is not a group on ℚ it's only a group on ℚ - 0
    -- i.e. can't divide by 0
   -- theory of iterations leads to multiplicative Nats but still has 0
   -- can talk about products of primes directly
   -- the set of compositions of a given function behaves like the
   -- non-zero Nats under addition
   -- the set of iterations of a given function behaves like the Nats
   -- under multiplication

 module NonZeroNat₂ where
  open Functions.Composition.Definition
  data NonZeroComp {A : Set} (f : A → A) : (A → A) → Set where
   unit : NonZeroComp f f
   _·_ : {h g : A → A} → NonZeroComp f h → NonZeroComp f g → NonZeroComp f (h ∘ g)
   
 

 module Primes where
  -- fundamental theorem of arithmetic: unique decomposition into products of powers of primes
  -- nth prime function
  -- https://primes.utm.edu/notes/faq/p_n.html
  -- Sierpinski's / Hardy / Wright "special constant" approach
  -- Wilson's theorem approach
  -- unique representation of products of primes:
  -- could have lists of Nats
  -- [] = 1
  -- (1 :: 0 :: 2 :: [])  → 2^1 * 3^0 * 5^2
  -- but to ensure no repetition, we need to make sure the biggest prime in the list has a non-zero exponent
  -- ∃ ∀
  {-
   connectives:
   ¬
   ∧
   ∨

   x ∧ y = ∧ x y
   x ∨ y = ∨ x y
   ∀ x, (f x) = ∀ f
   ∃ x, (f x) = ∃ f

   T x y = x
   F x y = y
   @ g f x = g (f x)
   ∘ R f g x = R (f x) (g x)

   ∧ (f x) (g x) = ∘ ∧ f g x
   ∨ (f x) (g x) = ∘ ∨ f g x 


   @xyz = x(yz)
   SKxy = Ky(xy) = y
   Sxyz = xz(yz)
   S(Kx)yz = Kxz(yz) = x(yz)
   @xyz = S(Kx)yz
   SNKxyz = Nx(Kx)yz
   Nx = S
   N = KS
   @ = S(KS)K
   S(KS)Kxyz = KSx(Kx)yz = S(Kx)yz = Kxz(yz) = x(yz)
   
   ∘ w x y z = w (x z) (y z)

   * x (y z) = x y z
   C x y z = x z y
   
   C N x (y z) = N (y z) x 
   
   

   http://sshieh.web.wesleyan.edu/wescourses/2013f/388/e-texts/Schonfinkel%20On%20the%20Building%20Blocks%20of%20Mathematical%20Logic.pdf
   page 11
   "For every predicate f, there exists a predicate g such that the propositional function fx & gx is not true of any object x"
   


   ∀ f, (∃ g, (∀ x, ¬ ((f x) ∧ (g x))))
   ∀ f ,(∃ g, (∀ x, ¬ (∧ (f x) (g x)))
   ∀ f, (∃ g , (∀ x, ¬ (∘ ∧ f g x)))
   ∀ f, (∃ g , (∀ x, (@ ¬ (∘ ∧ f g) x)))
   ∀ f, (∃ g , (∀ (@ ¬ (∘ ∧ f g)))
   ∀ f, (∃ g , (∀ (∘ @ (T ¬) (∘ ∧ f) g))
   ∀ f, (∃ g, (@ ∀ (∘ @ (T ¬) (∘ ∧ f)) g))
   ∀ f, (∃ (@ ∀ (∘ @ (T ¬) (∘ ∧ f))))


   ∀ f, (∘ ∃ (T (@ ∀ (∘ @ (T ¬)))) (∘ ∧) f)
   ∀ (∘ ∃ (T (@ ∀ (∘ @ (T ¬)))) (∘ ∧))
 
   ∀ (∘ ∃ (K (S (KS) K ∀ (∘ (S (KS) K) (K ¬)))) (∘ ∧))


   ∀ x, (∃ g, (∀ f, ¬ ((f x) ∧ (g x))))
   

   Q(x,f) = f' x


   ∧
   ∨
   ¬

   ∃ x, f(x)
   ∃ x, f(x) = ∃ x, f(x) ∧ f(x) = ∃ x, ~~(f(x) ∧ (fx)) = ~(∀x,~((f x) ∧ (f x))) = ~(Uff)

   _∘_ g f x = g (f x)
   _∘'_ h g f x = h (_∘' g f x) 
  -}
  

 module Integers where
  data ℤ : Set where
   zero : ℤ
   possuc : ℕ → ℤ 
   negsuc : ℕ → ℤ
  
 open Integers
 module NonZeroIntegers where
  data ℤ-0 : Set where
   possuc : ℕ → ℤ-0
   negsuc : ℕ → ℤ-0
 -- integers satisfy unique representation under this definition;
 -- unique representation allows the equality relation of the type theory to serve
 -- as the equivalence relation on the type, so given two equivalent objects x and y,
 -- a proof of P(x) can be turned into a proof of P(y)
 -- binary representations of integers
 -- finite integers
 -- integers as the free abelian group on 1 generator
 -- https://math.stackexchange.com/questions/62852/in-set-theory-how-are-real-numbers-represented-as-sets
 -- construction of Integers as 



 module Rationals where
  -- https://github.com/agda/agda-stdlib/blob/master/src/Data/Rational.agda#L35
  open NonZeroNats
  module Representations where
   module Fractions where
    data ℚ : Set where
     _/_ : ℤ → ℕ → ℚ
   module Fractions₂ where
    data ℚ : Set where
     _/_ : ℤ → ℕ* → ℚ
   module Fractions₃ where
    data ℚ : Set where
     _/_ : ℤ → (n : ℕ) → (n ≠ 0) → ℚ
   module Fractions₄ where
    data ℚ : Set where
     _÷_ : ℤ → (n : ℕ) → {p : ((n eq 0) ≡ false)} → ℚ

    _/_ : ℤ → (n : ℕ) → {p : ((n eq 0) ≡ false)} → ℚ
    (z / 0) {()}
    (z / (suc n)) {refl} = (z ÷ (suc n)) {refl}

    {-
    2/3 : ℚ
    2/3 = (possuc 1) / 3
    -}

   module Fractions₅ where
    data ℚ : Set where
     _÷_ : ℕ → (d : ℕ) → {p : ((d eq 0) ≡ false)} → ℚ

    _/_ : ℕ → (d : ℕ) → {p : ((d eq 0) ≡ false)} → ℚ
    (n / 0) {()}
    (n / (suc d)) {refl} = (n ÷ (suc d)) {refl}

    {-
    -- still doesn't work
    2/3 : ℚ
    2/3 = 2 / 3
    -}

    2/3 : ℚ
    2/3 = (2 / 3) {refl}

   
   module Fractions₆ where
    
    data ℚ : Set where
     _÷_ : ℕ → (d : ℕ) → {p : False (d ≟ 0)} → ℚ

    _/_ : ℕ → (d : ℕ) → {p : False (d ≟ 0)} → ℚ
    (x / 0) {()}
    (x / (suc y)) {unit} = (x ÷ (suc y)) {unit}

    2/3 : ℚ
    2/3 = (2 / 3) {unit}
   

   module MixedFractions where
    data ℚ : Set where
     _[_/_] : ℤ → ℕ → ℕ → ℚ
     
   -- rationals as the smallest field with characteristic zero
   module MixedFractions₂ where
    data ℚ : Set where
     _[_/_,_] : (w : ℤ) → (n : ℕ) → (d : ℕ) → (n ≠ 0) → ℚ

   {-
   module MixedFractions₃ where
    data ℚ : Set where
     _[_/_,_] : (w : ℤ) → (n : ℕ) → (d : ℕ) → | (n ≠ 0) | → ℚ
   -}

   module MixedFractions₄ where
    data ℚ : ℤ → ℕ → ℕ → Set where
     _[_/_] : (w : ℤ) → (n : ℕ) → (d : ℕ) → ℚ w n (suc d)
   
   module PrimeFactors where
    open BaseDefinitions.BaseTypes.List
    open NonZeroIntegers
    data ℚ : Set where
     one : ℚ
     𝕢 : ℤ-0 → List ℤ → ℚ

   module PrimeFactors₂ where
    open BaseDefinitions.BaseTypes.List
    open NonZeroIntegers
    data ℚ : Set where
     zero : ℚ
     one : ℚ
     q : ℤ-0 → List ℤ → ℚ

   module PrimeFactors₃ where
    -- denoting the nth prime, not saying that every Nat is prime
    data Prime : Set where
     p : ℕ → Prime

    data PrimeRat : Set where
     _/1 : Prime → PrimeRat
     1/  : Prime → PrimeRat

    -- almost; this is more like what we want but then this is the same
    -- cardinality as the reals; why? because the expansion is not required
    -- to be finite!
    ℚ : Set
    ℚ = ℕ → ℤ
    
    -- ratios of successive primes converge to 1
    -- https://math.stackexchange.com/questions/900364/do-the-ratios-of-successive-primes-converge-to-a-value-less-than-1
    

   module Stern-Brocot where
    -- Stern-Brocot tree and unique enumeration of rationals
    -- https://www.cs.ox.ac.uk/jeremy.gibbons/publications/rationals.pdf
    -- https://en.wikipedia.org/wiki/Stern%E2%80%93Brocot_tree
    -- Stern-Brocot tree respects equality and ordering of rationals
    -- Calkin-Wilf tree
    -- https://en.wikipedia.org/wiki/Calkin%E2%80%93Wilf_tree
    
    
    data ℚ : Set where
     one : ℚ
     L : ℚ → ℚ
     R : ℚ → ℚ

    1/ : ℚ → ℚ
    1/ one = one
    1/ (L x) = (R x)
    1/ (R x) = (L x)
    -- free magma as binary trees
    -- List Bool..
    -- [] = 1
    -- T = R
    -- F = L
    -- Easy to invert a list
    -- multiplicative inverse == map not
    -- semi-lexicographic ordering
    --

    {-
    -- not right! it's inverting the paths
    _≤_ : ℚ → ℚ → Set
    one ≤ one = ⊤
    (L x) ≤ one = ⊤
    (R x) ≤ one = ⊥
    one ≤ (L y) = ⊥
    (L x) ≤ (L y) = x ≤ y
    (R x) ≤ (L y) = ⊥
    one ≤ (R y) = ⊤
    (L x) ≤ (R y) = ⊤
    (R x) ≤ (R y) = x ≤ y

    ≤-refl : (q : ℚ) → q ≤ q
    ≤-refl one = unit
    ≤-refl (L x) = ≤-refl x
    ≤-refl (R x) = ≤-refl x
    -}

    {-
    ≤-sym : (q r : ℚ) → (q ≤ r) → (r ≤ q) → q ≡ r
    ≤-sym one r one≤r r≤one 
    -}
    -- need a toPrime function
   -- https://math.stackexchange.com/questions/181724/uniqueness-of-continued-fraction-representation-of-rational-numbers

   -- word problem for groups is undecidable
   -- word problem for finite simple groups is "uniformly solvable"
   -- word problem for abelian groups?
   -- Knuth-Bendix algorithm
   -- computable groups
   -- http://www.massey.ac.nz/~amelniko/survey.pdf
   module Stern-Brocot₂ where
    open BaseDefinitions.Sum
    open BaseDefinitions.BaseTypes.List
    open BaseDefinitions.BaseTypes.List.Operations
    open Boolean.Operations renaming (_eq_ to Bool-eq)
    open Functions.Iteration.Definition
    
    ℚ : Set
    ℚ = List Bool

    parent : ℚ → ℚ
    parent [] = []
    parent (y ∷ []) = []
    parent (x ∷ xs) = x ∷ (parent xs)

    _≤_ : ℚ → ℚ → Set
    [] ≤ [] = ⊤
    [] ≤ (false ∷ ys) = ⊥
    [] ≤ (true ∷ ys) = ⊤
    (false ∷ xs) ≤ [] = ⊤
    (false ∷ xs) ≤ (false ∷ ys) = xs ≤ ys
    (false ∷ xs) ≤ (true ∷ ys) = ⊤
    (true ∷ xs) ≤ [] = ⊥
    (true ∷ xs) ≤ (false ∷ ys) = ⊥
    (true ∷ xs) ≤ (true ∷ ys) = xs ≤ ys

    ≤-sub : {x : Bool} → {xs ys : List Bool} → (x ∷ xs) ≤ (x ∷ ys) → xs ≤ ys
    ≤-sub {true} {xs} {ys} p = p
    ≤-sub {false} {xs} {ys} p = p

    ≤-sub₂ : (x : Bool) → {xs ys : List Bool} → xs ≤ ys → (x ∷ xs) ≤ (x ∷ ys)
    ≤-sub₂ true {xs} {ys} p = p
    ≤-sub₂ false {xs} {ys} p = p
    
    ≤-refl : (x : ℚ) → x ≤ x
    ≤-refl [] = unit
    ≤-refl (false ∷ xs) = ≤-refl xs
    ≤-refl (true ∷ xs) = ≤-refl xs

    ≤-antisym : (x y : ℚ) → x ≤ y → y ≤ x → x ≡ y
    ≤-antisym [] [] p q = refl
    ≤-antisym [] (false ∷ ys) ()
    ≤-antisym [] (true ∷ ys) p ()
    ≤-antisym (false ∷ xs) [] p ()
    ≤-antisym (false ∷ xs) (false ∷ ys) p q = cong (λ qs → false ∷ qs) (≤-antisym xs ys p q)
    ≤-antisym (false ∷ xs) (true ∷ ys) p ()
    ≤-antisym (true ∷ xs) [] ()
    ≤-antisym (true ∷ xs) (false ∷ ys) ()
    ≤-antisym (true ∷ xs) (true ∷ ys) p q = cong (λ qs → true ∷ qs) (≤-antisym xs ys p q)

    
    ≤-trans : (x y z : ℚ) → x ≤ y → y ≤ z → x ≤ z
    ≤-trans [] y [] p q = unit
    ≤-trans [] [] (false ∷ zs) p ()
    ≤-trans [] (true ∷ ys) (false ∷ zs) p ()
    ≤-trans [] (false ∷ ys) (false ∷ zs) ()
    ≤-trans [] y (true ∷ zs) p q = unit
    ≤-trans (false ∷ xs) y [] p q = unit
    ≤-trans (false ∷ xs) [] (false ∷ zs) p ()
    ≤-trans (false ∷ xs) (true ∷ ys) (false ∷ zs) p ()
    ≤-trans (false ∷ xs) (false ∷ ys) (false ∷ zs) p q = proof
     where
      lemma1 : xs ≤ ys
      lemma1 = ≤-sub {false} {xs} {ys} p

      lemma2 : ys ≤ zs
      lemma2 = ≤-sub {false} {ys} {zs} q

      lemma3 : xs ≤ zs
      lemma3 = ≤-trans xs ys zs lemma1 lemma2
      
      proof = ≤-sub₂ false {xs} {zs} lemma3
      
    ≤-trans (false ∷ xs) y (true ∷ zs) p q = unit
    ≤-trans (true ∷ xs) [] z ()
    ≤-trans (true ∷ xs) (false ∷ ys) z ()
    ≤-trans (true ∷ xs) (true ∷ ys) [] p ()
    ≤-trans (true ∷ xs) (true ∷ ys) (false ∷ zs) p ()
    ≤-trans (true ∷ xs) (true ∷ ys) (true ∷ zs) p q = proof
     where
      lemma1 : xs ≤ ys
      lemma1 = ≤-sub {true} {xs} {ys} p

      lemma2 : ys ≤ zs
      lemma2 = ≤-sub {true} {ys} {zs} q

      lemma3 : xs ≤ zs
      lemma3 = ≤-trans xs ys zs lemma1 lemma2
      
      proof = ≤-sub₂ true {xs} {zs} lemma3

    
    ≤-total : (x y : ℚ) → (x ≤ y) ∨ (y ≤ x)
    ≤-total [] (false ∷ ys) = inr unit
    ≤-total [] [] = inl unit
    ≤-total [] (true ∷ ys) = inl unit
    ≤-total (false ∷ xs) (false ∷ ys) = proof
     where
      lemma1 : (xs ≤ ys) ∨ (ys ≤ xs)
      lemma1 = ≤-total xs ys

      lemma2 : (xs ≤ ys) ∨ (ys ≤ xs) → ((false ∷ xs) ≤ (false ∷ ys)) ∨ ((false ∷ ys) ≤ (false ∷ xs))
      lemma2 (inl p) = inl (≤-sub₂ false {xs} {ys} p)
      lemma2 (inr p) = inr (≤-sub₂ false {ys} {xs} p)
      
      proof = lemma2 lemma1
    ≤-total (false ∷ xs) (true ∷ ys) = inl unit
    ≤-total (false ∷ xs) [] = inl unit
    ≤-total (true ∷ xs) (true ∷ ys) = proof
     where
      lemma1 : (xs ≤ ys) ∨ (ys ≤ xs)
      lemma1 = ≤-total xs ys

      lemma2 : (xs ≤ ys) ∨ (ys ≤ xs) → ((true ∷ xs) ≤ (true ∷ ys)) ∨ ((true ∷ ys) ≤ (true ∷ xs))
      lemma2 (inl p) = inl (≤-sub₂ true {xs} {ys} p)
      lemma2 (inr p) = inr (≤-sub₂ true {ys} {xs} p)
      
      proof = lemma2 lemma1
    ≤-total (true ∷ xs) (false ∷ ys) = inr unit
    ≤-total (true ∷ xs) [] = inr unit

    _↝_ : ℚ → ℚ → Set
    q ↝ r = ∃ s ∈ ℚ , ((q ++ s) ≡ r)

    _↝L_ : ℚ → ℚ → Set
    q ↝L r = ∃ s ∈ ℚ , ((q ++ (false ∷ s)) ≡ r)

    _↝R_ : ℚ → ℚ → Set
    q ↝R r = ∃ s ∈ ℚ , ((q ++ (true ∷ s)) ≡ r)

    _↝*R_ : ℚ → ℚ → Set
    q ↝*R r = ∃ s ∈ ℚ , (∃ n ∈ ℕ , ((q ++ ((((λ l → true ∷ l) ** n) []) ++ s)) ≡ r))

    _is-yca-of_and_ : ℚ → ℚ → ℚ → Set
    s is-yca-of q and r = ((s ↝ q) ∧ (s ↝ r)) ∧ ((s' : ℚ) → ((s' ↝ q) ∧ (s' ↝ r)) → (s' ↝ s))

    q++[]=q : ∀ {i} {A : Set i} → (l : List A) → (l ++ []) ≡ l
    q++[]=q [] = refl
    q++[]=q (x ∷ xs) = cong (_∷_ x) (q++[]=q xs)

    ++-assoc : ∀ {i} {A : Set i} → (xs ys zs : List A) → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
    ++-assoc [] ys zs = refl
    ++-assoc (x ∷ xs) ys zs = proof
     where
      lemma1 : ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
      lemma1 = ++-assoc xs ys zs
      
      proof = cong (λ q → x ∷ q) lemma1

    restsEqual : ∀ {i} {A : Set i} (x y : A) → (xs ys : List A) → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
    restsEqual {i} {A} x y [] [] refl = refl
    restsEqual {i} {A} x y [] (y' ∷ ys) ()
    restsEqual {i} {A} x y (x' ∷ xs) [] ()
    restsEqual {i} {A} x .x (x' ∷ xs) (.x' ∷ .xs) refl = refl

    firstsEqual : ∀ {i} {A : Set i} (x y : A) → (xs ys : List A) → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
    firstsEqual {i} {A} x y [] [] refl = refl
    firstsEqual {i} {A} x y [] (y' ∷ ys) ()
    firstsEqual {i} {A} x y (x' ∷ xs) [] ()
    firstsEqual {i} {A} x .x (x' ∷ xs) (.x' ∷ .xs) refl = refl
    
    x∷-inj : ∀ {i} {A : Set i} (x : A) → {xs ys : List A} → (x ∷ xs) ≡ (x ∷ ys) → xs ≡ ys
    x∷-inj {i} {A} x {[]} {[]} p = refl
    x∷-inj {i} {A} x {[]} {(y ∷ ys)} ()
    x∷-inj {i} {A} x {(x' ∷ xs)} {[]} ()
    x∷-inj {i} {A} x {(x' ∷ xs)} {(.x' ∷ .xs)} refl = refl


    []-unique-id : ∀ {i} {A : Set i} → (x y : List A) → ((x ++ y) ≡ x) → y ≡ []
    []-unique-id x [] p = refl
    []-unique-id [] (y ∷ ys) ()
    []-unique-id (x ∷ xs) (y ∷ ys) p = proof
     where
      lemma1 : ((x ∷ xs) ++ (y ∷ ys)) ≡ (x ∷ xs)
      lemma1 = p
      
      lemma2 : (x ∷ (xs ++ (y ∷ ys))) ≡ ((x ∷ xs) ++ (y ∷ ys))
      lemma2 = refl

      lemma3 : (xs ++ (y ∷ ys)) ≡ xs
      lemma3 = x∷-inj x lemma1

      proof = []-unique-id xs (y ∷ ys) lemma3

    ++-no-inverses : ∀ {i} {A : Set i} (xs ys : List A) → ((xs ++ ys) ≡ []) → (xs ≡ []) ∧ (ys ≡ [])
    ++-no-inverses [] [] p = refl , refl
    ++-no-inverses [] (y ∷ ys) ()
    ++-no-inverses (x ∷ xs) [] ()
    ++-no-inverses (x ∷ xs) (y ∷ ys) ()

    ↝-refl : (q : ℚ) → q ↝ q
    ↝-refl q = ([] , q++[]=q q)

    ↝-antisym : (x y : ℚ) → x ↝ y → y ↝ x → x ≡ y
    ↝-antisym x y (s₁ , p₁) (s₂ , p₂) = proof
     where
      lemma1 : (x ++ s₁) ≡ y
      lemma1 = p₁

      lemma2 : (y ++ s₂) ≡ x
      lemma2 = p₂

      lemma3 : ((x ++ s₁) ++ s₂) ≡ (y ++ s₂)
      lemma3 = cong (λ q → q ++ s₂) lemma1


      lemma4 : ((x ++ s₁) ++ s₂) ≡ x
      lemma4 = ≡-trans lemma3 lemma2

      lemma5 : (x ++ (s₁ ++ s₂)) ≡ ((x ++ s₁) ++ s₂)
      lemma5 = ≡-sym (++-assoc x s₁ s₂)

      lemma6 : (x ++ (s₁ ++ s₂)) ≡ x
      lemma6 = ≡-trans lemma5 lemma4

      lemma7 : (s₁ ++ s₂) ≡ []
      lemma7 = []-unique-id x (s₁ ++ s₂) lemma6 


      lemma8 : (s₁ ≡ []) ∧ (s₂ ≡ [])
      lemma8 = ++-no-inverses s₁ s₂ lemma7

      lemma9 : (x ++ s₁) ≡ (x ++ [])
      lemma9 = cong (_++_ x) (first lemma8)

      lemma10 : (x ++ []) ≡ x
      lemma10 = q++[]=q x

      proof = ≡-trans (≡-sym lemma10) (≡-trans (≡-sym lemma9) lemma1)
   
    ↝-trans : (x y z : ℚ) → x ↝ y → y ↝ z → x ↝ z
    ↝-trans x y z (s₁ , p₁) (s₂ , p₂) = ((s₁ ++ s₂) , proof)
     where
      lemma1 : (x ++ s₁) ≡ y
      lemma1 = p₁

      lemma2 : (y ++ s₂) ≡ z
      lemma2 = p₂

      lemma3 : ((x ++ s₁) ++ s₂) ≡ (y ++ s₂)
      lemma3 = cong (λ q → q ++ s₂) lemma1
      
      lemma4 : ((x ++ s₁) ++ s₂) ≡ z
      lemma4 = ≡-trans lemma3 lemma2

      lemma5 : (x ++ (s₁ ++ s₂)) ≡ ((x ++ s₁) ++ s₂)
      lemma5 = ≡-sym (++-assoc x s₁ s₂)
      
      proof = ≡-trans lemma5 lemma4


    -- *not* total
    -- *not* infinitely divisible

    get-yca : (x y : ℚ) → ℚ
    get-yca [] y  = []
    get-yca (x ∷ xs) [] = []
    get-yca (x ∷ xs) (y ∷ ys) = if (Bool-eq x y) then (x ∷ (get-yca xs ys)) else []

    -- Implementation in Idris
    -- https://github.com/mcgordonite/idris-binary-rationals/blob/master/Data/QQ/SternBrocot.idr

    list-lemma1 : ∀ {i} {A : Set i} (xs : List A) → {x y : A} → (x ≡ y) → (x ∷ xs) ≡ (y ∷ xs)
    list-lemma1 {i} {A} xs {x} {y} p = cong (λ f → f xs) (cong _∷_ p)

    ↝-lemma1 : (x y : ℚ) → x ↝ y → (b : Bool) → (b ∷ x) ↝ (b ∷ y)
    ↝-lemma1 x y (s , p) b = (s , cong (λ q → b ∷ q) p)

    ↝-lemma3 : (x y : ℚ) → x ↝ y → (bs : List Bool) → (bs ++ x) ↝ (bs ++ y)
    ↝-lemma3 x y (s , p) bs = (s , ≡-trans (++-assoc bs x s) (cong (_++_ bs) p))
    yca-unique : (x y : ℚ) → (p₁ p₂ : (∃ yca ∈ ℚ , (yca is-yca-of x and y))) → (π₁ p₁) ≡ (π₁ p₂)
    yca-unique x y (yca₁ , (r₁ , f₁)) (yca₂ , (r₂ , f₂)) = ↝-antisym yca₁ yca₂ (f₂ yca₁ r₁) (f₁ yca₂ r₂)
{-
where
      lemma1 : yca₂ ↝ yca₁
      lemma1 = f₁ yca₂ r₂

      lemma2 : yca₁ ↝ yca₂
      lemma2 = f₂ yca₁ r₁
-}
     
    {-
    get-yca-lemma : (x y : ℚ) → (get-yca x y) is-yca-of x and y
    get-yca-lemma [] y  = ( ([] , refl) , (y  , refl)) , (λ s p → first p)
    get-yca-lemma (x ∷ xs)  [] = ( ((x ∷ xs)  , refl) , ([] , refl)) , (λ s p → second p) 
    get-yca-lemma (true ∷ xs) (true ∷ ys) = proof
     where
      lemma1 : (get-yca (true ∷ xs) (true ∷ ys)) ≡ (true ∷ (get-yca xs ys))
      lemma1 = refl

      lemma2 : (get-yca xs ys) is-yca-of xs and ys
      lemma2 = get-yca-lemma xs ys

      lemma3 : (get-yca xs ys) ↝ xs
      lemma3 = first (first lemma2)

      lemma4 : (get-yca xs ys) ↝ ys
      lemma4 = second (first lemma2)

      lemma5 : (true ∷ (get-yca xs ys)) ↝ (true ∷ xs)
      lemma5 = ↝-lemma1 (get-yca xs ys) xs lemma3 true

      lemma6 : (true ∷ (get-yca xs ys)) ↝ (true ∷ ys)
      lemma6 = ↝-lemma1 (get-yca xs ys) ys lemma4 true

      lemma7 : (s : ℚ) → ((s ↝ (true ∷ xs)) ∧ (s ↝ (true ∷ ys))) → (s ↝ (true ∷ (get-yca xs ys)))
      lemma7 s ((s₁ , p₁) , (s₂ , p₂)) = (s₃ , p₃)
       where
        sublemma1 : (s ++ s₁) ≡ (true ∷ xs)
        sublemma1 = p₁

        sublemma2 : (s ++ s₂) ≡ (true ∷ ys)
        sublemma2 = p₂


        s₄ : ℚ
        s₄ = π₁ lemma5
        
        sublemma3 : (true ∷ xs) ≡ ((true ∷ (get-yca xs ys)) ++ s₄)
        sublemma3 = ≡-sym (π₂ lemma5)

        sublemma4 : (s ++ s₁) ≡ ((true ∷ (get-yca xs ys)) ++ s₄)
        sublemma4 = ≡-trans sublemma1 sublemma3

        s₃
        p₃

      proof = (lemma5 , lemma6) , lemma7
    -}
   
    {-
    _≤₂_ : ℚ → ℚ → Set
    q ≤ r = s is the longest prefix of both q and r,
            youngest common ancestor of both q and r
    cases:
     q ≡ r                         q ≤ r 
     q contains r to the right      q ≤ r
     q contains r to the left;      q ≰ r
     r contains q to the left;      q ≤ r
     r contains q to the right;     q ≰ r
     
     case: s = q = r
       q ≤ r
     case: s = q ≠ r
       q ≤ r iff s contains r to the right
     case: s ≠ q
       q ≤ r iff s contains q to the left
       

    _<_ : ℚ → ℚ → Set
    q < r = s is the longest prefix of both q and r,
            youngest common ancestor of both q and r
            if r is contained to the right by s or
               q is contained to the left by s 

    _≤_ : ℚ → ℚ → Set
    _≤_ = reflexive closure of _<_
    -}

    data _≤₃_ : ℚ → ℚ → Set where
     refl : {q : ℚ} → q ≤₃ q
     L : (q : ℚ) → (q ++ (false ∷ [])) ≤₃ q
     R : (q : ℚ) → q ≤₃ (q ++ (true ∷ []))
     trans : (x y z : ℚ) → x ≤₃ y → y ≤₃ z → x ≤₃ z

    inv : ℚ → ℚ
    inv q = map not q


   module RationalBags where
    -- rationals as bags of primes with negative multiplicities
    -- rational is an element of the free abelian group over the primes w/
    -- multiplication

 open Rationals
 
 -- equivalence relation on the Rationals;
 -- can we give them unique representation?
 -- translation into reals via division algorithm
 -- binary representations of rationals
   
 
 module Reals where
  module BooleanExpansions where
   ℝ : Set
   ℝ = ℕ → Bool

  module BooleanExpansion2 where
   ℝ : Set
   ℝ = ℕ × (ℕ → Bool)

  module BooleanExpansion3 where
   open BaseDefinitions.BaseTypes.List
   ℝ : Set
   ℝ = List Bool × (ℕ → Bool)
  {-
  module BooleanExpansion4 where
   ℝ : Set
   ℝ = 
  -}

 -- continued fraction description
  -- uniqueness of representation
  module ContinuedFractions where
  module CauchySequences where
  module DedekindCuts where
  module DedekindCompleteTotallyOrderedField where
  -- https://hott.github.io/book/nightly/hott-online-1186-gee8923a.pdf
  -- HoTT Book; page 374; construction of reals as Dedekind cuts
  -- Ford circles
  -- Farey sequences
  -- approximation by mediants


 -- translation of terminating / repeating real power expansions into Rationals

 module Algebraic where
 -- solutions to polynomial equations
 module Constructible where
 -- numbers you can make with a compass and straight-edge
 module Computable where
 -- numbers you can write to a tape with a turing-machine
 module Complex where
  -- algebraic completion of the real numbers
  -- unique algebraic completion of the unique dedekind complete totally ordered field
  -- unique uniformly complete Archimedean field
  open Reals.BooleanExpansions
  ℂ : Set
  ℂ = ℝ × ℝ

 module Special where
 -- sqrt(2)      length of diagonal of unit square; irrational; algebraic
 -- e            f = f' 
 -- pi           period of exponential function; circumference of circle; transcendental
 

 module Tower where
  open Rationals.Representations.Fractions
  open Reals.BooleanExpansions
  open Complex
  ℕ→ℤ : ℕ → ℤ
  ℕ→ℤ zero = zero
  ℕ→ℤ (suc n) = possuc n

  -- ℤ→ℕ is absolute value; loses information
  ℤ→ℕ : ℤ → ℕ
  ℤ→ℕ zero = zero
  ℤ→ℕ (possuc n) = suc n
  ℤ→ℕ (negsuc n) = suc n
  
  ℤ→ℚ₀ : ℤ → ℚ
  ℤ→ℚ₀ z = z / 0

  {-
  -- ℚ₀→ℤ is the div function, divide the numerator by the denominator and drop the remainder; equivalent to floor
  -}

  {-
  ℚ₀→ℝ this is the full division algorithm, carried out to the end; can we create an Agda function ℕ → Bool that
  spits out those digits?
  -}
  {-
  ℝ→ℚ₀ , no meaningful translation back at this point?
  -}

  ℝ→ℂ : ℝ → ℂ
  ℝ→ℂ r = (r , λ x → false)

  

module Algebra where
{-
fundamental theorem of algebra
-}
 module Polynomials where

module Geometry where
{-

-}

{-
pythagorean theorem & euclidean distance formulae
euclidean metric a result of pure number theory?
 

-}

module ModalLogic where
 module Semantics1 where
  module Necessity where
   [] : ∀ {i j k} {W : Set i} (R : W → W → Set j) → W → (P : W → Set k) → Set (i ⊔ (j ⊔ k))
   [] {i} {j} {k} {W} _R_ w P = (u : W) → (w R u) → P u
 
  {-
  -- `Possibility` modality, interpretation 1
  <> : ∀ {i j k} {W : Set i} (R : W → W → Set j) → W → (P : W → Set k) → Set (i ⊔ (j ⊔ k))
  <> {i} {j} {k} {W} _R_ w P = ∃ u ∈ W , ((w R u) ∧ P u)
  -}

  module Possibility where
   open BaseDefinitions.Negation.Definition
   -- `Possibility` modality, interpretation 2
   <> : ∀ {i j k} {W : Set i} (R : W → W → Set j) → W → (P : W → Set k) → Set (i ⊔ (j ⊔ k))
   <> {i} {j} {k} {W} _R_ w P = ¬ ((u : W) → ((w R u) → (¬ (P u))))

  module Properties where
   open BaseDefinitions.Equality.Definition
   open BaseDefinitions.Negation.Definition
   open BaseDefinitions.Relations.BinaryRelations.Properties.Reflexivity
   open BaseDefinitions.Relations.BinaryRelations.Properties.Symmetry
   open BaseDefinitions.Relations.BinaryRelations.Properties.Transitivity
   open Functions.Composition.Definition
   open Necessity
   open Possibility
   []¬→¬<> : ∀ {i j k} {W : Set i} {R : W → W → Set j} → (P : W → Set k) → (w : W) → [] R w (¬ ∘ P) → ¬ (<> R w P)
   []¬→¬<> {i} {j} {k} {W} {R} P w []¬P-w <>P-w = <>P-w []¬P-w

   ¬<>→[]¬ : ∀ {i j k} {W : Set i} {R : W → W → Set j} → (P : W → Set k) → (w : W) → ¬ (<> R w P) → [] R w (¬ ∘ P)
   ¬<>→[]¬ {i} {j} {k} {W} {_R_} P w ¬<>P x wRx Px = proof
    where
     lemma1 : ¬ (¬ ((y : W) → w R y → (¬ (P y))))
     lemma1 = ¬<>P

     lemma2 : ¬ ((y : W) → w R y → (¬ (P y)))
     lemma2 f = (f x wRx) Px

     proof = lemma1 lemma2
    
   <>¬→¬[] : ∀ {i j k} {W : Set i} {R : W → W → Set j} → (P : W → Set k) → (w : W) → <> R w (¬ ∘ P) → ¬ ([] R w P)
   <>¬→¬[] {i} {j} {k} {W} {_R_} P w <>¬P []P = proof
    where
     lemma1 : ¬ ((u : W) → w R u → (¬ (¬ (P u))))
     lemma1 = <>¬P

     lemma2 : (u : W) → w R u → (P u)
     lemma2 = []P

     lemma3 : (u : W) → w R u → ¬ (¬ (P u))
     lemma3 u wRu ¬Pu = ¬Pu (lemma2 u wRu)

     proof = lemma1 lemma3
   {-
   ¬[]→<>¬ : ∀ {i j k} {W : Set i} {R : W → W → Set j} → (P : W → Set k) → (w : W) → ¬ ([] R w P) → <> R w (¬ ∘ P)
   ¬[]→<>¬ {i} {j} {k} {W} {_R_} P w ¬[]P []¬¬P = proof
    where
     lemma1 : ¬ ((x : W) → w R x → P x)
     lemma1 = ¬[]P

     lemma2 : (x : W) → w R x → (¬ (¬ (P x)))
     lemma2 = []¬¬P

     proof
   -}

   []→¬<>¬ : ∀ {i j k} {W : Set i} {R : W → W → Set j} → (P : W → Set k) → (w : W) → ([] R w P) → (¬ (<> R w (¬ ∘ P)))
   []→¬<>¬ {i} {j} {k} {W} {_R_} P w = proof
    where
     lemma1 : ([] _R_ w P) ≡ ((u : W) → (w R u) → P u)
     lemma1 = refl

     lemma2 :  (¬ (<> _R_ w (¬ ∘ P))) ≡ ¬ (¬ ((u : W) → (w R u) → (¬ (¬ (P u)))))
     lemma2 = refl

     lemma3 : ((u : W) → (w R u) → P u) → ((u : W) → (w R u) → (¬ (¬ (P u))))
     lemma3 f u wRu ¬Pu = ¬Pu (f u wRu) 

     lemma4 : ((u : W) → (w R u) → (¬ (¬ (P u)))) → ¬ (¬ ((u : W) → (w R u) → (¬ (¬ (P u)))))
     lemma4 f p = p f

     proof = lemma4 ∘ lemma3




   N-rule : ∀ {i j k} {W : Set i} {R : W → W → Set j} → ((Q : W → Set k) → (x y : W) → R x y → Q x → Q y) → (P : W → Set k) → ((w : W) → P w → [] R w P)
   N-rule {i} {j} {k} {W} {R} N P w Pw u wRu = N P w u wRu Pw

   implies : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
   implies A B = A → B

   comp₂ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l} (h : B → C → D) (f : A → B) (g : A → C) → A → D
   comp₂ h f g a = h (f a) (g a)


   K-rule : ∀ {i j k} {W : Set i} {R : W → W → Set j} → (P Q : W → Set k) → (w : W) → [] R w (comp₂ implies P Q) → [] R w P → [] R w Q
   K-rule {i} {j} {k} {W} {R} P Q w []P→Q []P u wRu = []P→Q u wRu ([]P u wRu)


   T-rule : ∀ {i j k} {W : Set i} {R : W → W → Set j} → (Reflexive R) → (P : W → Set k) → (w : W) → [] R w P → P w
   T-rule {i} {j} {k} {W} {R} Refl-R P w []P = []P w (Refl-R w)


   4-rule : ∀ {i j k} {W : Set i} {_R_ : W → W → Set j} → Transitive _R_ → (P : W → Set k) → (w : W) → ([] _R_ w P) → (u : W) → (w R u) → ([] _R_ u P)
   4-rule {i} {j} {k} {W} {R} R-trans P w []P u wRu v uRv = []P v (R-trans wRu uRv)


   B-rule : ∀ {i j k} {W : Set i} {_R_ : W → W → Set j} →  ((Q : W → Set k) → (x y : W) → x R y → Q x → Q y) → Reflexive _R_ → Transitive _R_ → (P : W → Set k) → (w : W) → P w → (u : W) → (w R u) → (<> _R_ u P)
   B-rule {i} {j} {k} {W} {_R_} N R-refl R-trans P w Pw u wRu []¬P-u = proof
    where
     lemma1 : (v : W) → u R v → ¬ (P v)
     lemma1 = []¬P-u

     lemma2 : (v : W) → u R v → P v
     lemma2 v uRv = N P w v (R-trans wRu uRv) Pw

     lemma3 : P u
     lemma3 = lemma2 u (R-refl u)

     lemma4 : ¬ (P u)
     lemma4 = lemma1 u (R-refl u)

     proof = lemma4 lemma3

   D-rule : ∀ {i j k} {W : Set i} {R : W → W → Set j} → (Reflexive R) → (P : W → Set k) → (w : W) → ([] R w P) → (<> R w P)
   D-rule {i} {j} {k} {W} {_R_} Refl-R P w []P []¬P = []¬P w (Refl-R w) ([]P w (Refl-R w))

   5-rule : ∀ {i j k} {W : Set i} {_R_ : W → W → Set j} → (Symmetric _R_) → (Transitive _R_) → (P : W → Set k) → (w : W) → (<> _R_ w P) → (u : W) → (w R u) → (<> _R_ u P)
   5-rule {i} {j} {k} {W} {_R_} R-sym R-trans P w <>P-w u wRu []¬P-u = proof
    where
     uRw : u R w
     uRw = R-sym wRu


     []¬P-w : (x : W) → (w R x) → (¬ (P x))
     []¬P-w x wRx = subproof
      where
       uRx : u R x
       uRx = R-trans uRw wRx

       subproof = []¬P-u x uRx
  
   
     -- []¬P-u : (v : W) → (u R v) → (¬ (P v)) 
     proof = <>P-w []¬P-w

{-
data LC : Set where
 v : Nat → LC
 abs : Nat →  LC → LC
 app : LC → LC → LC
-}



--------------------------------------------------------------------



module SKI where
  module Syntax1 where
   open BaseDefinitions.BaseTypes.Nat
   data Term : Set where
    $ : Nat → Term
    S : Term
    K : Term
    I : Term
    _·_ : Term → Term → Term

  module Syntax1Semantics1 where
   open Syntax1
   module OneStep where
    Δ : Term → Term
    Δ (I · x) = x
    Δ ((K · x) · y) = x
    Δ ((( S · x) · y) · z) = (x · z) · (y · z)
    Δ q = q

   module Equivalence where
    open BaseDefinitions.Product
    open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
    open BaseDefinitions.Equality.Definition
    open OneStep
    open Functions.Iteration.Definition
    _~_ : Term → Term → Set
    C₁ ~ C₂ = (x y : Term) → ∃ m ∈ ℕ , (∃ n ∈ ℕ , (((Δ ** m) C₁) ≡ ((Δ ** n) C₂)))

--------------------------------------------------------------------


  module Syntax2 where
   open BaseDefinitions.BaseTypes.List
   open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
   data Term : Set where
    $ : ℕ → Term
    S : Term
    K : Term
    I : Term
    [_] : List Term → Term
--------------------------------------------------------------------


  module Syntax3 where
   open BaseDefinitions.BaseTypes.List
   open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)

   data Base : Set where
    S : Base
    K : Base
    I : Base
    $ : ℕ → Base

   data Term : Set where
    <_,_> : Base → Term → Term

--------------------------------------------------------------------


  module Syntax4 where
   open BaseDefinitions.BaseTypes.List
   open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)

   data Base : Set where
    S : Base
    K : Base
    I : Base
    $ : ℕ → Base

   data Term : Set where
    [_,_] : Base → List Term → Term

   

  module Syntax4Semantics1 where
   open Syntax4
   open BaseDefinitions.BaseTypes.List
   module OneStep where
    Δ : Term → Term
    Δ ([ I , ( ([ a , xs ]) ∷ ys) ]) = [ a , (xs ++ ys) ]
    Δ ([ K , ( ([ a , xs ]) ∷ b ∷ ys) ]) = [ a , (xs ++ ys) ]
    Δ ([ S , ( ([ a , xs ]) ∷ [ b , ys ] ∷ c ∷ zs) ]) = [ a , (xs ++ (c ∷ [ b , (ys  ++ (c ∷ [])) ] ∷ zs)) ]
    Δ q = q

--------------------------------------------------------------------

  -- can we find a representation that makes terms unique?
  -- can we find a representation that works well with composition?
  --  what do we mean by that?
  --  (Δ ** n) 
  module Syntax5 where
   open BaseDefinitions.BaseTypes.List
   open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
   data Combinator : Set where
    S : Combinator 
    K : Combinator
    I : Combinator

   data Base : Set where
    $ : ℕ → Base
    ` : Combinator → Base

   data Term : Set where
    [_,_] : Base → List Term → Term

   data Expression : Set where
    [_,_] : Combinator → List Term → Expression
   
  module Syntax5Semantics1 where
   open Syntax5




---------------------------------------------

  module Syntax6 where
   open BaseDefinitions.BaseTypes.List
   open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ; suc to 𝕤)
   open BaseDefinitions.BaseTypes.Vector

   data Combinator : ℕ → Set where
    S : Combinator 3
    K : Combinator 2
    I : Combinator 1

   data Atom : Set where
    $ : ℕ → Atom
    ` : {n : ℕ } → Combinator n → Atom

   data Term : Set where
    [_,_] : Atom → List Term → Term

   data Expression : Set where
    [_,_] : {n : ℕ} → Combinator n → Vector Term n → Expression

   `_` : Expression → Term
   ` [ c , v ] ` = [ ` c , toList v ]

  module Syntax6Semantics1 where
   open BaseDefinitions.BaseTypes.List
   open BaseDefinitions.BaseTypes.Vector
   open Syntax6
   Δ : Expression → Term
   Δ [ I , ([ x , xs ] ∷ []) ] = [ x , xs ]
   Δ [ K , ([ x , xs ] ∷ y ∷ []) ] = [ x , xs ]
   Δ [ S , ([ x , xs ] ∷ [ y , ys ] ∷ z ∷ []) ] = [ x , (xs ++ (z ∷ ([ y , (ys ++ (z ∷ [])) ]) ∷ [])) ]


---------------------------------------------


  module Syntax7 where
   open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
   data Combinator : ℕ → Set where
    S : Combinator 3
    K : Combinator 2
    I : Combinator 1

  {-
  module Syntax7Semantics1 where
   open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
   open Syntax7
   Δ : ∀ {i} {n : ℕ} → Combinator n → {A : Set i} → Tree A n → Tree A n
   Δ S (a ∷ b ∷ c ∷ []) =
   Δ K (a ∷ b ∷ []) = 
   Δ I (a ∷ []) = 
 -}
---------------------------------------------


  module Semantics2 where
   open BaseDefinitions.BaseTypes.List renaming (_∷_ to _,_; _++_ to List++)
   open Syntax2
   module OneStep where
    Δ : Term → Term
    Δ [ I , x , xs ] = [ x , xs ]
    Δ [ K , x , y , xs ] = [ x , xs ]
    Δ [ S , x , y , z , xs ] = [ x , z , [ y , z , [] ] , xs ]
    Δ e = e

    Term→ListTerm : (x : Term) → List Term
    Term→ListTerm [ [] ] = []
    Term→ListTerm S = (S , [])
    Term→ListTerm K = (K , [])
    Term→ListTerm I = (I , [])
    Term→ListTerm ($ n) = (($ n) , [])
    Term→ListTerm [ T ] = T
    
 
    _++_ : Term → Term → Term
    x ++ y = [ List++ (Term→ListTerm x) (Term→ListTerm y) ]

   open OneStep public
   module Normalization where
    open BaseDefinitions.Equality.Definition
    open BaseDefinitions.Product
    open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
    open Functions.Iteration.Definition
    _↝_ : (x y : Term) → Set
    x ↝ y = ∃ n ∈ ℕ , (((Δ ** n) x) ≡ y)



   module Equivalence where
    open Normalization
    open BaseDefinitions.Equality.Definition
    open BaseDefinitions.Product
    open Functions.Iteration.Definition
    _~_ : Term → Term → Set
    x ~ y = (z : Term) → ∃ w ∈ Term ,  (((x ++ z) ↝ w) ∧ ((y ++ z) ↝ w))

   module Properties where
    open BaseDefinitions.Equality.Definition
    open BaseDefinitions.Equality.Properties
    open BaseDefinitions.Sum
    open BaseDefinitions.Product
    open BaseDefinitions.BaseTypes.Nat
    open BaseDefinitions.BaseTypes.Bool
    open BaseDefinitions.Relations.Properties.Reflexivity
    open BaseDefinitions.Relations.Properties.Transitivity
    open BaseDefinitions.BaseTypes.Fin.Definition
    open BaseDefinitions.BaseTypes.Fin.Operations
    open BaseDefinitions.BaseTypes.Fin.Properties
    open BaseDefinitions.BaseTypes.List renaming (_++_ to List++)
    open BaseArithmetic.Operations
    open Functions.Composition.Definition
    open Functions.Iteration.Definition
    open FunctionArithmetic.ExponentialLaws
    open Normalization
    open Equivalence

    ↝-refl : Reflexive _↝_
    ↝-refl x = (0 , refl)

    
    ↝-trans : Transitive _↝_
    ↝-trans {x} {y} {z} (m , refl) (n , refl) = (n + m , proof)
     where
      lemma1 : ((Δ ** m) x) ≡ y
      lemma1 = refl
      
      lemma2 : ((Δ ** n) y) ≡ z
      lemma2 = refl

      lemma3 : ((Δ ** (n + m)) x) ≡ (((Δ ** n) ∘ (Δ ** m)) x)
      lemma3 = cong (λ q → q x) (≡-sym (+-law Δ n m))

      lemma4 : (((Δ ** n) ∘ (Δ ** m)) x) ≡ ((Δ ** n) ((Δ ** m) x))
      lemma4 = refl
      
      lemma5 : ((Δ ** n) ((Δ ** m) x)) ≡ ((Δ ** n) y)
      lemma5 = cong (λ q → (Δ ** n) q) lemma1

      proof  = ≡-trans lemma3 lemma4


    {-
    Δ[x ++ y] = Δ[Δx ++ y] → Δx = x
    Δ[x ++ y] = Δx ++ y → Δx ≠ x

    Δx=x → [Δx]++y = Δ[Δx ++ y] = Δ [ x ++ y ]
    Δx=x → 
    -}
    ⌋_⌊ : (x : Term) → Set
    ⌋ x ⌊ = Δ x ≡ x

    isNormal : Term → Bool
    isNormal [ I , a , xs ] = false
    isNormal [ K , a , b , xs ] = false
    isNormal [ S , a , b , c , xs ] = false
    isNormal q = true

    I-lemma₁ : (a : Term) → (xs : List Term) → (Δ [ I , a , xs ]) ≠ [ I , a , xs ]
    I-lemma₁ a xs ()

    I-lemma₀ : (a : Term) → (xs : List Term) → (Δ ([ I , a , [] ] ++ [ xs ])) ≡ ((Δ [ I , a , [] ]) ++ [ xs ])
    I-lemma₀ a xs = refl

    K-lemma₁ : (a b : Term) → (xs : List Term) → (Δ [ K , a , b , xs ]) ≠ [ K , a , b , xs ]
    K-lemma₁ a b xs ()

    K-lemma₀ : (a b : Term) → (xs : List Term) → (Δ ([ K , a , b , [] ] ++ [ xs ])) ≡ ((Δ [ K , a , b , [] ]) ++ [ xs ])
    K-lemma₀ a b xs = refl

    S-lemma₁ : (a b c : Term) → (xs : List Term) → (Δ [ S , a , b , c , xs ]) ≠ [ S , a , b , c , xs ]
    S-lemma₁ a b c xs ()

    S-lemma₀ : (a b c : Term) → (xs : List Term) → ((Δ [ S , a , b , c , [] ]) ++ [ xs ]) ≡ ((Δ [ S , a , b , c , [] ]) ++ [ xs ])
    S-lemma₀ a b c xs = refl

    

    {-
    Δ-lemma₀ : (x y : Term) → (Δ (x ++ y)) ≡ (Δ ((Δ x) ++ y)) → (Δ x) ≡ x
    Δ-lemma₀ [ I , a , xs ] y p = proof
     where
      xs++y = (List++ xs (Term→ListTerm y))
      
      lemma1 : (Δ ([ I , a , xs ] ++ y)) ≡ Δ ([ I , a , xs++y ] )
      lemma1 = refl

      lemma2 : Δ ([ I , a , xs++y ] ) ≡ [ a , xs++y ]
      lemma2 = refl

      lemma3 : Δ ([ I , a , xs++y ] ) ≡ (Δ ((Δ [ I , a , xs ]) ++ y))
      lemma3 = p

      lemma4 : (Δ [ I , a , xs ]) ≡ [ a , xs ]
      lemma4 = refl

      lemma5 : Δ ([ I , a , xs++y ] ) ≡ (Δ ([ a , xs ] ++ y))
      lemma5 = transport (λ q → Δ ([ I , a , xs++y ] ) ≡ (Δ (q ++ y))) lemma4 lemma3

      lemma6 : [ a , xs++y ] ≡ (Δ ([ a , xs ] ++ y))
      lemma6 = lemma5

      lemma7 : (Δ ([ I , a , xs ] ++ y)) ≡ (Δ ([ a , xs ] ++ y))
      lemma7 = lemma5

      lemma8 : [ a , xs++y ] ≡ ([ a , xs ] ++ y)
      lemma8 = refl

      lemma9 : ([ a , xs ] ++ y) ≡ (Δ ([ a , xs ] ++ y))
      lemma9 = ≡-trans (≡-sym lemma8) (≡-trans (≡-sym lemma2) (≡-trans (≡-sym lemma1) lemma7))

      {-
      lemma10 : [ I , a , xs ] is not a normal form, but [ a , xs ] might be, in which case it's of a finite
      set of forms
      -}
      

      proof 
    Δ-lemma₀ [ K , a , b , xs ] y p = refl
    Δ-lemma₀ [ S , a , b , c , xs ] y p = refl
    Δ-lemma₀ q y p = refl
    -}
    {-
    ++-lemma : (x : Term) (ys : List Term) (zs : Term) → ([ x , ys ] ++ zs) ≡ [ x , (Term→ListTerm ([ ys ] ++ zs)) ]
    ++-lemma x [] [ [] ] = refl
    ++-lemma x [] [ z , zs ] = proof
     where
      -- lemma0 : ( [ [] ] ++ [ z ∷ zs ]) ≡ 
      
      lemma1 : (Term→ListTerm ([ [] ] ++ [ z ∷ zs ])) ≡ (z ∷ zs)
      lemma1 = refl

      lemma2 : ([ x , [] ] ++ [ z ∷ zs ]) ≡ [ x ∷ z ∷ zs ]
      lemma2 = refl

      proof
    ++-lemma x (y ∷ ys) zs = refl
    -}

    {-
    (Δ ((Δ x) ++ y))) ∧ ((Δ x) = x)
    ∨
    ((Δ (x ++ y)) ≡ ((Δ x) ++ y)) ∧ ((Δ x) ≠ x)
     --  only in the case of:
     --   [ I , a , xs ]
     --   [ K , a , b , xs ]
     --   [ S , a , b , c , xs ]
    -}
    {-
    Δ-lemma : (x y : Term) → ((Δ (x ++ y)) ≡ (Δ ((Δ x) ++ y))) ∨ ((Δ (x ++ y)) ≡ ((Δ x) ++ y))
    Δ-lemma [ [] ] [ [] ] = inl refl
    Δ-lemma [ [] ] [ y , ys ] = inl proof
     where
      lemma0 : ([ [] ] ++ [ y , ys ]) ≡ [ y , ys ]
      lemma0 = refl

      lemma1 : (Δ [ [] ]) ≡  [ [] ]
      lemma1 = refl

      lemma2 : [ y , ys ] ≡ ((Δ [ [] ]) ++ [ y , ys ])
      lemma2 = refl
      
      proof = cong Δ (≡-trans lemma0 lemma2)
    Δ-lemma S y = inl refl
    Δ-lemma [ S , [] ] y = inl refl
    Δ-lemma [ S , a , [] ] y = inl refl
    Δ-lemma [ S , a , b , [] ] y = inl refl
    Δ-lemma [ S , a , b , c , xs ] y = inr {!!}
    Δ-lemma K y = inl refl
    Δ-lemma [ K , [] ] = λ y → inl refl
    Δ-lemma [ K , a , [] ] = λ y → inl refl
    Δ-lemma [ K , a , b , xs ] = λ y → inr {!!}
    Δ-lemma I y = inl refl
    Δ-lemma [ I , [] ] = λ y → inl refl
    Δ-lemma [ I , a , xs ] = λ y → inr {!!}
    Δ-lemma ($ n) y = inl refl
    Δ-lemma [ ($ n) , xs ] = λ y → inl refl
    Δ-lemma [ [ T ] , xs ] = λ y → inl refl
    -}
    {-
    Δᵐx↝Δⁿx,m>n : 
    -}

    

    {-
    -- "Translation invariance property"
    -- https://en.wikipedia.org/wiki/Partially_ordered_group
    -- Partially ordered monoid?
    x↝y→xz↝yz : {x y : Term} → x ↝ y → (z : Term) → (x ++ z) ↝ (y ++ z)
    x↝y→xz↝yz {x} {y} (0 , Δ⁰x=y) z = proof
     where
      lemma1 : x ≡ ((Δ ** 0) x)
      lemma1 = refl

      lemma2 : ((Δ ** 0) x) ≡ y
      lemma2 = Δ⁰x=y

      lemma3 : x ≡ y
      lemma3 = lemma2

      lemma4 : (x ++ z) ≡ (y ++ z)
      lemma4 = cong (λ q → q ++ z) lemma3

      lemma5 : (y ++ z) ↝ (y ++ z)
      lemma5 = ↝-refl (y ++ z)

      lemma6 : (x ++ z) ↝ (y ++ z)
      lemma6 = (transport (λ P → P ↝ (y ++ z)) (≡-sym lemma4) lemma5)

      proof = lemma6
    x↝y→xz↝yz {[ S , [] ]} {y} (n , ΔⁿS=y) z = proof
     where
      lemma1 : (n : Nat) → ((Δ ** n) [ S , [] ]) ≡ [ S , [] ]
      lemma1 0 = refl
      lemma1 (suc n) = subproof
       where
        sublemma1 : ((Δ ** (suc n)) [ S , [] ]) ≡ ((Δ ∘ (Δ ** n)) [ S , [] ])
        sublemma1 = refl

        sublemma2 : ((Δ ∘ (Δ ** n)) [ S , [] ]) ≡ (Δ  ((Δ ** n) [ S , [] ]))
        sublemma2 = refl

        sublemma3 : ((Δ ** n) [ S , [] ]) ≡ [ S , [] ]
        sublemma3 = lemma1 n

        sublemma4 : (Δ  ((Δ ** n) [ S , [] ])) ≡ (Δ [ S , [] ])
        sublemma4 = cong Δ sublemma3

        sublemma5 : (Δ [ S , [] ]) ≡ [ S , [] ]
        sublemma5 = refl

        subproof = sublemma4
        
      lemma2 : y ≡ [ S , [] ]
      lemma2 = ≡-trans (≡-sym ΔⁿS=y) (lemma1 n)
      --lemma2 = ≡-trans (≡-sym ΔⁿS=y) (lemma1 n)

      

      proof = ( 0 , cong (λ q → q ++ z) (≡-sym lemma2)) 
    x↝y→xz↝yz {x} {y} ((suc n) , Δˢⁿx=y) z = proof
     where
      
      lemma1 : ((Δ ** ℕ[ (n - zero) ]) x) ≡ ((Δ ** n) x)
      lemma1 = cong (λ q → ((Δ ** q) x)) (ℕ[n-0]=n n)

      lemma2 : (y ++ z) ↝ (y ++ z)
      lemma2 = ↝-refl (y ++ z)

      lemma3 : ((Δ ** (suc n)) (x ++ z)) ≡ ((Δ ∘ (Δ ** n)) (x ++ z))
      lemma3 = refl
      
      lemma4 : ((Δ ∘ (Δ ** n)) (x ++ z)) ≡ (Δ ((Δ ** n) (x ++ z)))
      lemma4 = refl

      lemma5 : ((Δ ** n) x) ↝ y
      lemma5 = (1 , Δˢⁿx=y)

      -- ((Δ ** n) x) ++ z ≠ (Δ ** n) (x ++ z)
      -- but there should exist m such that ((Δ ** n) x) ++ z = (Δ ** (n + m)) (x ++ z)
      
      lemma6 : (((Δ ** n) x) ++ z) ↝ (y ++ z) 
      lemma6 = x↝y→xz↝yz {((Δ ** n) x)} {y} lemma5 z

      -- lemma7 :
      -- Δ (((Δ ** n) x) ++ z) ≡ (((Δ ** n)
      -- 

      proof = {!!} -- = ≡-trans lemma1 Δˢⁿx=y -- :((Δ ** n) x ++ z) ≡ (y ++ z)
    -}
    {-
    x↝y→x~y : {x y : Term} → x ↝ y → x ~ y
    x↝y→x~y x↝y z = ( yz , (xz↝yz , yz↝yz))
     where
      yz = y ++ z
      xz↝yz = x↝y→xz↝yz x↝y z
      yz↝yz = ↝-refl yz
    -}
  {-
  module Syntax3 where
   open BaseDefinitions.BaseTypes.List
   open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
   data Term : Set where
    $ : ℕ → Term
    S : Term
    K : Term
    I : Term
    
   data Expression : Set where
    [_] : List Term → Expression
    
  -}


  module Playground where
   open Syntax1
   open Syntax1Semantics1

   π₂ : Term
   π₂ = (S · K)

   {-
   π₂xy=y :  
   -}

  module Playground2 where
   open BaseDefinitions.Product renaming (_,_ to pair)
   open BaseDefinitions.Equality.Definition
   open BaseDefinitions.BaseTypes.List renaming (_∷_ to _,_; _++_ to List++)
   open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
   open Syntax2
   open Semantics2
   open Semantics2.Normalization
   open Functions.Iteration.Definition

   Π₂ : Term
   Π₂ = [ S , K , [] ] 

   Π₂xy↝y : (x y : Term) → (Π₂ ++ [ x , y , [] ]) ↝ [ y , [] ]
   Π₂xy↝y x y = proof
    where
     C : Term
     C = Π₂ ++ [ x , y , [] ]
     
     lemma : C ≡ [ S , K , x , y , [] ]
     lemma = refl
     
     Δ⁰ : ((Δ ** 0) C) ≡ [ S , K , x , y , [] ]
     Δ⁰ = refl

     Δ¹ : ((Δ ** 1) C) ≡ [ K , y , [ x , y , [] ] , [] ]
     Δ¹ = refl

     Δ² : ((Δ ** 2) C) ≡ [ y , [] ]
     Δ² = refl

     proof = pair 2 refl


   {-
   π₂xy~y : (x y : Term) → (π₂ ++ [ x , y , [] ]) ~ [ y , [] ]
   π₂xy~y x y = proof
    where
     C : Term
     C = π₂ ++ [ x , y , [] ]
     
     lemma : C ≡ [ S , K , x , y , [] ]
     lemma = refl
     
     Δ⁰ : ((Δ ** 0) C) ≡ [ S , K , x , y , [] ]
     Δ⁰ = refl

     Δ¹ : ((Δ ** 1) C) ≡ [ K , y , [ x , y , [] ] , [] ]
     Δ¹ = refl

     Δ² : ((Δ ** 2) C) ≡ [ y , [] ]
     Δ² = refl

     proof 
   -}

module Equivalence where
 open BaseDefinitions.Relations

module Sets where
 module PropositionalSets where
  Subset : ∀ {i} (A : Set i) → Set ((lsuc lzero) ⊔ i)
  Subset {i} A = A → Set

 -- finite sets with HITs
 -- https://dl.acm.org/citation.cfm?id=3167085
 

 module BooleanSets where
  open BaseDefinitions.BaseTypes.Bool
  subset : ∀ {i} (A : Set i) → Set i
  subset {i} A = A → Bool
 

module Multiset where
-- Coq stdpp apparently has something like a multiset?
-- https://gitlab.mpi-sws.org/iris/stdpp
-- HITs
-- quotient types; quotient a list by its order
-- abelian groups as bags with negative multiplicity?
-- https://github.com/inc-lc/ilc-agda/blob/master/Postulate/Bag-Nehemiah.agda#L35

-- commutative monoids as bags with only positive multiplicity?
-- free commutative monoid
-- lists = free monoid?
-- https://en.wikipedia.org/wiki/Free_monoid
-- the things that are true about the free object of some class of structures,
-- as a consequence of the structure laws for that class, are exactly the things
-- that are true all possible structures in that class, as a consequence of those
-- same structure laws
-- ℕ as "the" free monoid on 1 generator
-- ℤ as "the" free group on 1 generator
-- http://www.eelis.net/research/math-classes/mscs.pdf



module Cardinality where
 {-
 -- bijection as 1-1 correspondence; 
 -- existence of 1-1 correspondence of elements as same cardinality
 -- is an equivalence relation
 -- https://en.wikipedia.org/wiki/Finite_set#Necessary_and_sufficient_conditions_for_finiteness
 
 -- correspondence to some natural number
 -- correspondence to Fin; bijection with Fin
 -- listability
 -- every subset of S has a least and greatest element
 -- countability vs. uncountability; cantor's theorem
 -- A is finite  iff  for all B subset of A, f:A->B is a bijection implies A=B.
 -- Kuratowski finiteness
 -- S can be given a total ordering which is well-ordered both forwards and backwards
 -- Every surjective function from S onto itself is 1-1
 -- S is empty or every partial ordering of S contains a maximal element
 -- Dedekind infiniteness: the existence of a bijection between it and some proper subset of itself
-}
---------------------------------------------------------------------------------------
 module ListabilityFiniteness where
  open BaseDefinitions.Equality.Definition
  open BaseDefinitions.Product
  open BaseDefinitions.BaseTypes.List
  {-
  Finite : ∀ {i} (A : Set i) → Set i
  Finite A = ∃ l ∈ (List A) , ((x : A) → ((x ∈ l) ∧ ((y : A) → (y ∈ l - x) → x ≠ y)))
  -}
  -- highly dependent on relationships between sets, Lists, and Nats
  -- how to define the x ∈ l relationship?
  -- how to define the l - x operation?
  -- certainly can't be based on the value of x, it has to be based on that particular *occurrence*
  -- of x in this list, essentially based on position
  
 module Special where
 -- empty
 -- singleton
 -- n element
 -- aleph_0 = first countable infinity = size of Nat
 -- cardinality of continuum = size of Real
 
-- correspondence between finite cardinalities and individual natural numbers
-- 
      
module Functors where
{-
 homomorphism is a mapping that preserves connectedness
 an invertible homomorphism preserves both connectedness *and* disconnectedness;
 this suffices to preserve the entire structure; no information is lost in either direction
 invertible homomorphism, i.e. isomorphism, as "same structure"
 bijection as isomorphism and notion of "same structure" on sets

-}

module CombinatoryLogic where
 {- General specification of combinators -}
 {-
 SKI
 BCKW
 BRKD
 Iota
 -}
 {-
 Combinatorial completeness
 -}

module Prolog where
 open BaseDefinitions.Equality.Definition
 open BaseDefinitions.Product
 open BaseDefinitions.BaseTypes.Bool
 open BaseDefinitions.BaseTypes.Bool.Operations
 open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
 open BaseArithmetic.BooleanPredicates
 open BaseDefinitions.BaseTypes.List
 open Boolean.Operations renaming (_eq_ to Bool-eq)
 open Containers
 data Term : Set where
  const : ℕ → Term
  blank : ℕ → Term
  var : ℕ → Term

 Term-eq : Term → Term → Bool
 Term-eq (const c)  (const d)  = c eq d
 Term-eq (const c)  x          = false
 Term-eq (blank b1) (blank b2) = b1 eq b2
 Term-eq (blank b1) x          = false
 Term-eq (var v)    (var w)    = v eq w
 Term-eq (var v)    x          = false

 data Pred : Set where
  pred : ℕ → Pred

 data Atom : Set where
  _[_] : Pred → List Term → Atom

 Hom : (Term → Term) → Set
 Hom h = (t : Term) → ∃ c ∈ ℕ , ( t ≡ (const c)) → (h t) ≡ t

 Subst : (Term → Term) → Set
 Subst s = (t : Term) → ((∃ c ∈ ℕ , (t ≡ (const c))) → (s t) ≡ t) ∧ ((∃ b ∈ ℕ , (t ≡ (blank b)) → (s t) ≡ t))



 lookup : ∀ {i} {A : Set i} → (A → A → Bool) → List A → A → Bool
 lookup {i} {A} P [] a = false
 lookup {i} {A} P (x ∷ xs) a = (P a x) or (lookup P xs a)

 retrieve : ∀ {i j} {A : Set i} {B : Set j} → (A → A → Bool) → List (A × B) → A → Maybe B
 retrieve {i} {j} {A} {B} P [] a = Nothing
 retrieve {i} {j} {A} {B} P ((x , b) ∷ xs) a = if (P a x) then (Just b) else (retrieve P xs a)

 apply-Maybe-subst : Maybe Term → Term → Term
 apply-Maybe-subst Nothing t = t
 apply-Maybe-subst (Just x) t = x

 get-Maybe-subst : List (Term × Term) → Term → Maybe Term
 get-Maybe-subst l t = retrieve Term-eq l t
 
 apply-subst : List (Term × Term) → Term → Term
 apply-subst l t = apply-Maybe-subst (get-Maybe-subst l t) t

 hom : Term → Term → Bool
 hom (const c)  (const d)   = c eq d
 hom (const c)  (blank b)   = true
 hom (const c)  (var v)     = true
 hom (blank b)  (const c)   = true
 hom (blank b1) (blank b2)  = true
 hom (blank b)  (var v)     = true
 hom (var v)    x           = true



 hom-unify : Term → Term → Maybe (List (Term × Term))
 hom-unify (const c)  (const d)   = if (c eq d) then (Just []) else Nothing
 hom-unify (const c)  (blank b)   = Just (((blank b)  , (const c)) ∷ [])
 hom-unify (const c)  (var v)     = Just (((var v)    , (const c)) ∷ [])
 hom-unify (blank b)  (const c)   = Just (((blank b)  , (const c)) ∷ [])
 hom-unify (blank b1) (blank b2)  = Just (((blank b1) , (blank b2)) ∷ [])
 hom-unify (blank b)  (var v)     = Just (((var v)    , (blank b)) ∷ [])
 hom-unify (var v)    x           = Just (((var v)    , x) ∷ [])
 
 subst : Term → Term → Bool
 subst (const c)  (const d)  = c eq d
 subst (const c)  (blank b)  = false
 subst (const c)  (var v)    = true
 subst (blank b)  (const c)  = false
 subst (blank b1) (blank b2) = b1 eq b2
 subst (blank b)  (var v)    = true
 subst (var v)    x          = true

 subst-unify : Term → Term → Maybe (List (Term × Term))
 subst-unify (const c)  (const d)  = if (c eq d) then (Just []) else Nothing
 subst-unify (const c)  (blank b)  = Nothing
 subst-unify (const c)  (var v)    = Just (((var v) , (const c)) ∷ [])
 subst-unify (blank b1) (const c)  = Nothing
 subst-unify (blank b1) (blank b2) = if (b1 eq b2) then (Just (((blank b1) , (blank b2)) ∷ [])) else Nothing
 subst-unify (blank b1) (var v)    = Just (((var v ) , (blank b1)) ∷ [])
 subst-unify (var v)    x          = Just (((var v ) , x) ∷ [])
  
 -- union-find
 

module Computability where
 {-
 Combinatory logic
 Lambda calculus
 Rewrite systems
 Turing machines
 General recursive functions
 Mu recursive function
 Post canonical system
 Queue automata
 Transition system
 Labeled transition system
 Cell automata
 Pushdown automata
 Primitive recursive functions
 Nondeterministic finite state automaton
 Deterministic finite state machine
 subleq
 x86
 Arithmetical definability of general recursive functions
--------------------------------------------------------------

Finding a good set of combinators:


∧ 
pair x y f = f x y    -- reorders, but doesn't remove, repeat, or regroup
first x y = x         -- removes, but doesn't reorder, repeat, or regroup
second x y = y        -- 

pair pair x y = y pair x
pair (second pair) x y = y (second pair) x


church-encoding





Transistor model:
 wires/switches                      equalities between truth-values; possibly directed
 transistors/electronic switch       equalities between truth-value and existence of an equality
 always off                          false
 always on                           true
 short-circuit                       1 == 0

logic gates, just individually
  not a ; out := 
    a := (0 == out)

  -------- out
    |a
  ------- 0

    
  and a b ; out := 
    a := (1 == x)
    b := (x == out)
  
  ------ 1
   |a
   |b
  ------- out

  or a b ; out :=
    a := (1 == out)
    b := (1 == out)
 
  --------------- 1
    |a     |b
  -------------- out 

  serial vs. parallel circuits

  ((a and b) or ((c or d))

  ----------------- 1
   |c  |d   |a
  ------   ---
     |      |b
   ------------- out
 
  ((a and b) and (b or c))

  ------------- 
    a |  |   | 
      ---|   |
         |b
         ------
 

  1 == x
 
(A & B) | (B & C) = ((A & B) | B) & ((A & B) | C) = (A & B) & ((A & B) | C) = (A & B) | C
(A & B) | (B & C)

 (B & A) | (B & C) = B & (A | C)

  A   B   C   A & B    B & C     A & B | B & C     A & B | C
  0   0   0   0        0         0                 0
  1   0   0   0        0         0                 0
  0   1   0   0        0         0                 0
  1   1   0   1        0         1                 1
  0   0   1   0        0         0                 1       not equal!

 can't decompose into a DNF with no repeated vars.
 
 


(A & B) | B = B?
(A | B) & B = B?

 A & B | B & C
000  0
100  0
010  0
110  1
001  0
101  0
011  1
111  1

-- you gain one bit of information going through a switch
-- & gate is two switches in series:
     * 2 bits of information if ON;  1 state out of 4 specified uniquely;  log₂(4) = 2
     * narrowed down to 3 out of the 4 states; 3 * (4/3) = 4;  log₂(4/3) = ?
     * narrowed down to 2 out of the 4 states; 2 * (4/2) = 4;  log₂(2) = 1
     * narrowed down to 4 out of the 4 states; 4 * (4/4) = 4;  log₂(1) = 0
-- how much information do you gain going through an AND gate?
     * log₂(4)   = 2  when out = 1
     * log₂(4/3) = ?  when out = 0
-- how much information do you gain going through an OR gate?
     * log₂(4/3) = ?  when out = 1
     * log₂(4)   = ?  when out = 0
-- 
   
   

---------             -------------   
 |    |                 |      |
 A    B                 A      C        
 |    |                 |___   |
 B    C                     |  |
 |    |                     BBBB
-------- out                |  |
                       -------------   how many bits of information here?

<imode> that result is what I use to teach people about breaking down boolean statements.
`if (x) { if (y) { do_thing(); } }`                 == if(x && y) { do_thing(); }`   == join
`if (x) { do_thing(); } else if(y) { do_thing(); }  == if(x || y) { do_thing(); }`   == seq
`if (x) {} else { do_thing(); }                     == if(~x) { do_thing(); }        == not

true         = \x.\y.x                  K₁ = T
false        = \x.\y.y                  K₂ = F
y            = \x.\f.(f (x x f))        Y
if-then-else = \x.\y.\b.(b x y)
join         = \b₁.\b₂.(b₁ (b₂ T F) F)                        
seq          = \b₁.\b₂.(b₁ T (b₂ T F))
not          = \b₁.\b₂.

Y Y K₂ x = K₂ (Y Y K₂) x = x
Y N M x = M (N N M) x
Y N Y x = Y (N N Y) x = x 

Y (YK) Y x y z = Y (YK (YK) Y) x y z = 

Y (N N Y) x = x

if (x) { if (y) {do_thing();} else {dont_thing();} else {dont_thing();}
imode> that result is what I use to teach people about breaking down boolean statements.
2:54 PM `if (x) { if (y) { do_thing(); } }` == `if(x && y) { do_thing(); }`
2:55 PM `if (x) { do_thing(); } else if(y) { do_thing(); }`
2:56 PM == `if(x || y) { do_thing(); }
\x.\y.((\x₁.\x₂.\b₁.(b₁ x₁ x₂)) ((\y₁.\y₂.\b₂.(b₂ y₁ y₂)) DO DONT y) DONT x) 

Y f x = f (x f x)

Y (Y) x y = Y (x (Y) x) y = 
Y (YK) x y = YK (x (YK) x) y = K (x (YK) x K (x (YK) x)) y = 
Y (KY) x y = KY(x (KY) x) y = Y y

N such that Nx = x
Y K K x y = K (K K K) x y = K K K y = K y

Y K x = K (x K x)
Y K K x = K (K K K) x = K K K = K
Y Y K x = Y (K Y K) x = K Y K (x (K Y K) x) = Y (x (K Y K) x)
Y K Y Z x = K (Y K Y) Z x = Y K Y x = K (Y K Y) x = Y K Y = K (Y K Y)

Y x y = x (y x y)

--------------------------------------
Y x f = f (x x f)

Y K x y = x (K x K) y
Y K K x y = K (K K K) x y = K K K y = K y
Y K K K x y = K (K K K) K x y = K K K x y = K x y = x
Y K K K K x y = K (K K K) K K = K K K K x y = K K x y = K y
Y K K K K K x y = K (K K K) K K = K K K K K x y = K K K x y = K x y = x

can never do Y _ x, unless it's the last operation because that ends with a stuck term. so we will never do Y _ x
can you ever do Y x _ ?

Y K x y = x (K K x) y

Y x N -- to be able to do this, we must have already rotated x and N, which means we must have already used the Y combinator on x
Y x K y = K (x x K)

But x could have been in a subterm:

Y N q, or Y q N, where x is a subterm of q
But x could have only been grouped into a complex term by some previous application of the Y combinator.

Y x f = f (x x f)


Y K x y = x (K K x) y = x K x y 
Y (KK) x y = x (KK (KK) x) y = x (KK) y


Y f x = f (x f x)
Y K x y = x (K x K) y = x x y
Y (KY) x y = x (K Y x (KY)) y = x (Y (KY))
Y (YK) x y = x (Y K x (YK)) y = x (K (x K x) (YK)) y = x (x K x) y

Y K x y = K (x K x) y = x K x y
Y (YK) x y = YK (x (YK)x) y
Y K Y x y = K (Y K Y) x y = Y K Y x y
Y Y K x y = Y (K Y K) x y = K Y K (x (K Y K) x) y = Y (x (K Y K) x) y = x (KYK) x (y (x (KYK) x) y)
 = x Y x (y (x Y x) y)
Y Y (KK) x y = Y (KK Y (KK)) x y = KKY(KK)(x (KKY(KK)) x)y = K(KK)(x (KKY(KK)) x)y = KKy = K
Y T F x y = T (F T F) x y = F T F y = F T 

[YTT]xy = T (T T T) x y = T T T x y = T x y = x
[YTF]xy = YTFxy = T(FTF)xy = F T F x y = F x y = y
[YFT]xy = YFTxy = F(TFT)xy = x y
[YFF]xy = YFFxy = F(FFF)xy = x y
YTT = T
YTF = F
YFT = I
YFF = I

YYTT = Y (T Y T) x y = T Y T (x (T Y T) x) y = 
YYTFxy = T(TYT)Fxy = TYTxy = Yxy

Y x f = f (x x f)
Y T T x y = T (T T T) x y = T T T y = T y
Y T F x y = F (T T F) x y = x y


Y f x = f (x f x)
Y (YTF) x y = YTF (x (YTF) x) = 

Y f x = f x x

Y T x = T (x x) = x
Y (FF) x = FF x x = x x   = D



Y x f = f x x
Y Y F = F Y Y = Y

Y f x = f (x x)

Y 


https://en.wikipedia.org/wiki/SKI_combinator_calculus#Boolean_logic
T = \x.\y.x  = K
F = \x.\y.y  = SK

_NOT = FT
T F T = F
F F T = T

_OR_ = T
T T T = T
T T F = T
F T T = T
F T F = F

__AND = F
T T F = T
T F F = F
F T F = F
F F F = F

(A B AND) OR C
(A B F) T C

Y NOT = (Y NOT) NOT
Y OR 

I = YF
K = T
S = 





https://www.sciencedirect.com/science/article/pii/0304397589901503
 "If g is a monotone boolean function depending on all its variables, 
 the property that each prime implicant of g intersects each prime clause 
 of g in a singleton is a well-known necessary condition for g to be 
 computable by a formula with no repeated variable, and only using the connectives 
 and, or. We prove that the condition is also sufficient. 
 Our proof uses matroid theory."

De Morgan duality

Claude Shannon "Switching algebra"
Huntington's postulates for boolean algebra
Duality principle: every Boolean formula remains true if we interchange ANDs with ORs and 0s for 1s
Post's lattice;
 * maximal clones of Post's lattice
  * monotonic connectives               only change F to T, don't change T to F
  * affine                              each variable either always or never affects the value
  * self-dual connectives               are their own de-morgan dual
  * truth-preserving                    assigns T to all vars T
  * false-preserving                    assigns F to all vars F

compositions of AND/OR/NOT
 functional completeness;
 classical propositional logic
 termination and complexity guarantees are direct
  time-complexity linear in depth of circuit
  space-complexity linear in size of circuit
 boolean satisfiability == consistency check
 P vs NP!
 CNF   Conjunctive normal form: AND of ORs
 DNF   Disjunctive normal form: OR of ANDs
 NNF   Negation normal form
 
functional completeness vs. combinatorial

internal feedback
  memory cells
  finite state machine

can we make an FSM that implements the action of a combinator?

different model depending on whether:
internal memory as a separate I/O, i.e. it’s only referenced once during the course of the function, not continually, but still persistent over the course of multiple calls
probably simpler
the hard-drive model
referenced continually, but not persistent; has to be always running; the RAM memory model;
we want it to be obvious when the state transition, i.e. execution step, is “complete”
external feedback
turing completeness achieved by adding external feedback to the FSM, i.e. the infinite tape



 -}

--------------------------------------------------------------

--------------------------------------------------------------
{-
State transition system:
https://en.wikipedia.org/wiki/Transition_system

-}

 module TransitionSystem where
  module TransitionSystem1 where
   record TransitionSystem : Set₁ where
    field
     S : Set
     ⇒ : S → S → Set
  -- aka (Unindexed) Abstract Rewriting System
  -- aka (Unlabeled) Directed Graph
  -- aka Set with binary relation

  module LabeledTransitionSystem1 where
   record LabeledTransitionSystem : Set₁ where
    field
     S : Set
     L : Set
     ⇒ : S → L → S → Set
     
   -- aka Indexed Abstract Rewriting System
   -- aka Labeled Directed Graph
   
   -- Every labelled state transition system {S,L,→} is bijectively a function
   -- ξ from S to ℙ[L × S] (the powerset of "S indexed by L")
   -- ?


  module Properties where
   open BaseDefinitions.Product
   open BaseDefinitions.BaseTypes.Unit
   open BaseDefinitions.Equality.Definition
   open TransitionSystem1
   open LabeledTransitionSystem1
   
   Theorem1 : TransitionSystem → LabeledTransitionSystem  
   Theorem1 T = record {S = S; L = ⊤; ⇒ = (λ p a q → ⇒ p q)}
    where
     open TransitionSystem T


   isSimulationRelation :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     let L = LabeledTransitionSystem.L lts in
     (R : S → S → Set) → Set
   isSimulationRelation lts R = (x y : S) → R x y →  (x' : S) → (l : L) → (⇒ x l x') → ∃ y' ∈ S , ((⇒ y l y') ∧ (R x' y')) 
    where
     open LabeledTransitionSystem lts


   simulates :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     (x y : S) → Set₁
   simulates lts x y = ∃ R ∈ (S → S → Set) , ((isSimulationRelation lts R) ∧ (R x y))
    where
     open LabeledTransitionSystem lts

   -- show that (lts : LabeledTransitionSystem) → isPreorder (simulates lts)
   
   simulates-refl :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     (x : S) → simulates lts x x
   simulates-refl lts x = (R , (isSim-R , Rxx))
    where
     open LabeledTransitionSystem lts

     R : S → S → Set
     R p q = p ≡ q

     isSim-R : isSimulationRelation lts R
     isSim-R p .p refl p' l ⇒plp' = (p' , (⇒plp' , refl))

     Rxx : R x x
     Rxx = refl
   

   simulates-trans :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     (x y z : S) → simulates lts x y → simulates lts y z → simulates lts x z
   simulates-trans lts x y z (R₁ , (isSim-R₁ , R₁xy)) (R₂ , (isSim-R₂ , R₂yz)) = (R , (isSim-R , Rxz))
    where
     open LabeledTransitionSystem lts
     
     R : S → S → Set
     R p r = ∃ q ∈ S , ((R₁ p q) ∧ (R₂ q r))

     {-
     lemma1 : ∃ y' ∈ S , ((⇒ y l y') ∧ (R x' y'))
     lemma1 = isSim-R₁ x y R₁xy x' l ⇒plp' ?

     lemma2 : ∃ z' ∈ S , ((⇒ z l z') ∧ (R y' z'))
     lemma2 = isSim-R₂ y z R₂yz
     -}     

     isSim-R : isSimulationRelation lts R
     isSim-R p q Rpq p' l ⇒plp' = ( q' , (⇒qlq' , Rp'q'))
      where
       lemma3 : ∃ r ∈ S , ((R₁ p r) ∧ (R₂ r q))
       lemma3 = Rpq

       r : S
       r = π₁ lemma3

       R₁pr : R₁ p r
       R₁pr = first (π₂ lemma3)

       R₂rq : R₂ r q
       R₂rq = second (π₂ lemma3)

       lemma4 : ∃ r' ∈ S , ((⇒ r l r') ∧ (R₁ p' r'))
       lemma4 = isSim-R₁ p r R₁pr p' l ⇒plp'

       r' : S
       r' = π₁ lemma4

       ⇒rlr' : ⇒ r l r'
       ⇒rlr' = first (π₂ lemma4)

       R₁p'r' : R₁ p' r'
       R₁p'r' = second (π₂ lemma4)

       lemma5 : ∃ q' ∈ S , ((⇒ q l q') ∧ (R₂ r' q'))
       lemma5 = isSim-R₂ r q R₂rq r' l ⇒rlr'


       q' = π₁ lemma5

       R₂r'q' : R₂ r' q'
       R₂r'q' = second (π₂ lemma5)

       ⇒qlq' = first (π₂ lemma5)
       Rp'q' = (r' , (R₁p'r' , R₂r'q'))
     
     Rxz : R x z
     Rxz = (y , (R₁xy , R₂yz))

  -- "simulates lts" is the largest simulation relation over lts
  -- note how the definitions need to be relativized to the universe hierarchy
  --
   similar :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     (x y : S) → Set₁
   similar lts x y = (simulates lts x y) ∧ (simulates lts y x)

   similar-refl :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     (x : S) → similar lts x x
   similar-refl lts x = (simulates-refl lts x , simulates-refl lts x)

   similar-symm :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     (x y : S) → similar lts x y → similar lts y x
   similar-symm lts x y (p , q) = q , p

   similar-trans :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     (x y z : S) → similar lts x y → similar lts y z → similar lts x z
   similar-trans lts x y z (p₁ , q₁) (p₂ , q₂) = (simulates-trans lts x y z p₁ p₂ , simulates-trans lts z y x q₂ q₁)

  -- similarity of separate transition systems
  {-
   When comparing two different transition systems (S', Λ', →') and (S", Λ", →"), the basic notions of simulation and similarity can be used by forming the disjoint composition of the two machines, (S, Λ, →) with S = S' ∐ S", Λ = Λ' ∪ Λ" and → = →' ∪ →", where ∐ is the disjoint union operator between sets. 
  -}

  --Bisimulation
   isBisimulationRelation :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     let L = LabeledTransitionSystem.L lts in
     (R : S → S → Set) → Set
   isBisimulationRelation lts R = ((x y : S) → R x y → (x' : S) → (l : L) → (⇒ x l x') → ∃ y' ∈ S , ((⇒ y l y') ∧ (R x' y'))) ∧ ((x y : S) → R x y → (y' : S) → (l : L) → (⇒ y l y') → ∃ x' ∈ S , ((⇒ x l x') ∧ (R x' y')))
    where
     open LabeledTransitionSystem lts

   bisimilar :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     (x y : S) → Set₁
   bisimilar lts x y = ∃ R ∈ (S → S → Set) , ((isBisimulationRelation lts R) ∧ (R x y))
    where
     open LabeledTransitionSystem lts

   bisimilar-refl :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     (x : S) → bisimilar lts x x
   bisimilar-refl lts x = (_≡_ , ((left , right) , refl ))
    where
     open LabeledTransitionSystem lts
     
     left : (x y : S) → x ≡ y → (x' : S) → (l : L) → (⇒ x l x') → ∃ y' ∈ S , ((⇒ y l y') ∧ (x' ≡ y'))
     left x .x refl x' l ⇒xlx' = (x' , (⇒xlx' , refl))

     right : (x y : S) → x ≡ y → (y' : S) → (l : L) → (⇒ y l y') → ∃ x' ∈ S , ((⇒ x l x') ∧ (x' ≡ y'))
     right x .x refl x' l ⇒xlx' = (x' , (⇒xlx' , refl))

   -- converse relations
  -- counter-examples of mutual simulation but no bisimulation:

   bisimilar-symm :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     (x y : S) → bisimilar lts x y → bisimilar lts y x
   bisimilar-symm lts x y (R , ((left , right) , Rxy)) = (R' , ((left' , right') , R'yx))
    where
     open LabeledTransitionSystem lts

     R' : S → S → Set
     R' x y = R y x

     left' : (x y : S) → R' x y → (x' : S) → (l : L) → (⇒ x l x') → ∃ y' ∈ S , ((⇒ y l y') ∧ (R' x' y'))
     left' x y R'xy x' l ⇒xlx' = right y x R'xy x' l ⇒xlx'
     
     right' : (x y : S) → R' x y → (y' : S) → (l : L) → (⇒ y l y') → ∃ x' ∈ S , ((⇒ x l x') ∧ (R' x' y'))
     right' x y R'xy y' l ⇒yly' = left y x R'xy y' l ⇒yly'
     
     R'yx : R' y x
     R'yx = Rxy

   bisimilar-trans :
    (lts : LabeledTransitionSystem) →
     let S = LabeledTransitionSystem.S lts in
     (x y z : S) → bisimilar lts x y → bisimilar lts y z → bisimilar lts x z
   bisimilar-trans lts x y z (R₁ , ((left₁ , right₁) , R₁xy)) (R₂ , ((left₂ , right₂) , R₂yz)) = (R , ((left , right) , Rxz))
    where
     open LabeledTransitionSystem lts
     R : S → S → Set
     R p r = ∃ q ∈ S , ((R₁ p q) ∧ (R₂ q r))

     {-
     lemma1 : (p q : S) → R₁ p q → (p' : S) → (l : L) → (⇒ p l p') → ∃ q' ∈ S , ((⇒ q l q') , (R₁ p' q'))
     lemma1 = left₁
     -}

     left : (x y : S) → R x y → (x' : S) → (l : L) → (⇒ x l x') → ∃ y' ∈ S , ((⇒ y l y') ∧ (R x' y'))
     left p r (q , (R₁pq , R₂qr)) p' l ⇒plp' = (r' , (⇒rlr' , Rp'r'))
      where
       lemma1 : ∃ q' ∈ S , ((⇒ q l q') ∧ (R₁ p' q'))
       lemma1 = left₁ p q R₁pq p' l ⇒plp'     

       q' : S
       q' = π₁ lemma1
       
       ⇒qlq' : ⇒ q l q'
       ⇒qlq' = first (π₂ lemma1)
       
       R₁p'q' : R₁ p' q'
       R₁p'q' = second (π₂ lemma1)

       lemma2 : ∃ r' ∈ S , ((⇒ r l r') ∧ (R₂ q' r'))
       lemma2 = left₂ q r R₂qr q' l ⇒qlq'

       r' : S
       r' = π₁ lemma2
       
       ⇒rlr' : ⇒ r l r'
       ⇒rlr' = first (π₂ lemma2)

       R₂q'r' : R₂ q' r'
       R₂q'r' = second (π₂ lemma2)

       Rp'r' : R p' r'
       Rp'r' = (q' , (R₁p'q' , R₂q'r'))
     
     right : (x y : S) → R x y → (y' : S) → (l : L) → (⇒ y l y') → ∃ x' ∈ S , ((⇒ x l x') ∧ (R x' y'))
     right p r (q , (R₁pq , R₂qr)) r' l ⇒rlr' = (p' , (⇒plp' , Rp'r'))
      where
       lemma1 : ∃ q' ∈ S , ((⇒ q l q') ∧ (R₂ q' r'))
       lemma1 = right₂ q r R₂qr r' l ⇒rlr'

       q' : S
       q' = π₁ lemma1

       ⇒qlq' : ⇒ q l q'
       ⇒qlq' = first (π₂ lemma1)

       R₂q'r' : R₂ q' r'
       R₂q'r' = second (π₂ lemma1)

       lemma2 : ∃ p' ∈ S , ((⇒ p l p') ∧ (R₁ p' q'))
       lemma2 = right₁ p q R₁pq q' l ⇒qlq'

       p' : S
       p' = π₁ lemma2
       
       ⇒plp' : ⇒ p l p'
       ⇒plp' = first (π₂ lemma2)

       R₁p'q' : R₁ p' q'
       R₁p'q' = second (π₂ lemma2)


       Rp'r' : R p' r'
       Rp'r' = (q' , (R₁p'q' , R₂q'r'))
     Rxz = (y , (R₁xy , R₂yz))


  --relational definition of bisimulation
  --fixed-point definition of bisimulation
  --game-theoretical definition of bisimulation
  --coalgebraic definition of bisimulation
  --Simulation preorder
  --Van Benthem's theorem: propositional modal logic is the fragment of FOL invariant/closed under bisimulation
--------------------------------------------------------------
 {-
  Turing machine:
  https://en.wikipedia.org/wiki/Turing_machine
 -}
 module TuringMachine where
  open BaseDefinitions.Sum
  open BaseDefinitions.Product
  open BaseDefinitions.Negation.Definition
  open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
  open BaseDefinitions.BaseTypes.Bool
  open BaseDefinitions.BaseTypes.Fin
  module TuringMachine1 where
   record TuringMachine : Set₁ where
    field
     Q : Set
     Γ : Set
     b : Γ
     Σ : Γ → Set
     Σ-no-b : ¬ (Σ b)
     q₀ : Q
     F : Q → Set
  module TuringMachine2 where
   record TuringMachine : Set where
    field
     NF : ℕ   -- number of non-final states
     Γ : ℕ
     -- b : Γ; b = some Fin (suc Γ); can define b as Γ and Σ as some Fin Γ
     -- Σ : subset of Γ without b
     Σ : Fin Γ
     -- q₀ : Q; q₀ = some Fin (suc Q); can define q₀ as Q
     -- F : subset of Q; could include b
     F : ℕ    -- number of final states
     q₀ : (Fin NF) ∨ (Fin F)
     δ : (Fin NF) × Fin (suc Γ) → ((Fin NF) ∨ (Fin F)) × (Fin (suc Γ) × Bool)
     
    
    

-- minimal Turing complete turing machine
-- super-Turing computability:
-- https://www.univ-orleans.fr/lifo/Members/Jerome.Durand-Lose/Recherche/Publications/2008_UC_WorkPC.pdf
-- Bekenstein bound: https://en.wikipedia.org/wiki/Bekenstein_bound
-- Bremermann's limit: https://en.wikipedia.org/wiki/Bremermann%27s_limit
-- Black-hole information paradox : https://en.wikipedia.org/wiki/Black_hole_information_paradox
-- Holographic principle: https://en.wikipedia.org/wiki/Holographic_principle
-- Malament-Hogarth spacetime: https://en.wikipedia.org/wiki/Malament%E2%80%93Hogarth_spacetime
-- Kerr metric: https://en.wikipedia.org/wiki/Kerr_metric
-- A programming language for Turing machines: https://web.stanford.edu/class/archive/cs/cs103/cs103.1132/lectures/19/Small19.pdf

--------------------------------------------------------------
 {-
   Queue automata:
   https://en.wikipedia.org/wiki/Queue_automaton
 -}
 module QueueAutomaton where
  open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
  open BaseDefinitions.BaseTypes.Fin 
  open BaseDefinitions.BaseTypes.List
  open BaseDefinitions.Product
  module QueueAutomaton1 where
   record QueueAutomaton : Set₁ where
    field
     Q : Set                        -- states
     Γ : Set                        -- queue alphabet, needs to be finite
     Σ : Q → Set                   -- subset of the input alphabet
     $ : Γ                          -- initial queue symbol
     s : Q                          -- start state
     δ : Q × Γ → Q × List Γ        -- transition function

   -- problems: Γ is not necessarily finite, and neither is the subset Σ
   -- equality on the set might not necessarily be decidable
   -- membership in the subset Σ might not necessarily be decidable
  
  module QueueAutomaton2 where
   record QueueAutomaton : Set₁ where
    field
     Q : Set                         -- states
     s : Q                           -- start state
     Γ : ℕ                           -- queue alphabet; specified as Nat which defines a range of Nats 0 to Γ
                                    -- use some finite prefix of the Nats as the queue alphabet; input alphabet is
                                    -- some proper prefix of this queue alphabet, and Γ is then guaranteed to be outside it
                                    -- so we can use Γ as the initial queue symbol
     Σ : Fin Γ                       -- input alphabet; specified as some subset of the set of Nats from 0 to Γ - 1
     δ : Q × Fin (suc Γ) → Q × List (Fin (suc Γ))         -- transition function

  module QueueAutomaton3 where
   record QueueAutomaton : Set where
    field
     Q : ℕ                          -- set of states;
                                    -- start state = Q
     Γ : ℕ                         -- queue alphabet;
                                    -- initial queue symbol = Γ
     Σ : Fin Γ
     δ : Fin (suc Q) × Fin (suc Γ) → Fin (suc Q) × List (Fin (suc Γ))

  -- while that fixes the problems of the previous example, it's still a bit too specific
  -- ideally we would encompass everything that can reasonably satisfy the queue automaton conditions
  -- so we should probably assume that our alphabets can be any finite sets with a decidable equality
  -- relation defined on them; it should probably be a member of Set as well, just for good measure.
  -- let's abstract this over the universe hierarchy while we're at it:
  -- as you can see in the Cardinality module though there are many different ways to formulate the notion of
  -- finiteness, infiniteness, cardinality etc..
  -- similarly we may want to adjust what we mean when we say that the set has decidable equality
  -- so let's abstract over that as well
  module QueueAutomaton4 where
   record QueueAutomaton {i} : Set (lsuc i) where
    field
     Q : Set i                                                   -- set of states
     s : Q                                                       -- start state
     Γ : Set                                                     -- queue alphabet
     $ : Γ                                                       -- initial queue symbol
     ⟪_⟫<∞ : Set → Set                                          -- the "is finite" predicate
     _has≚ : Set → Set                                          -- the "has decidable equality" predicate
     ℙ[_] : Set → Set                                           -- power-set relation
     _∈_,_ : {A : Set} → (x : A) → (S : ℙ[ A ] ) → Set       -- set-inclusion relation  
     Γ-α : (⟪ Γ ⟫<∞ ) ∧ (Γ has≚ )                               -- gamma satisfies the finiteness and decidable equality criteria
     Σ : ℙ[ Γ ]                                                  -- Σ is a subset of Γ, not equal to Γ
     δ : Q × Γ → Q × List Γ                                     -- transition function


 -- decomposition 

 {-  
 Cell automata

 Pushdown automaton
 Finite state machine
 -}

 {-
 Turing completeness
 Unsolvability of halting problem by Turing machines
 -}


module FormalLanguages where
-- https://en.wikipedia.org/wiki/Formal_language
-- alphabet
-- bijection `code` with Fin n for some n ∈ ℕ
-- there is an equivalence defined on the alphabet by a = b iff code(a) = code(b)
-- a string is a list of characters in some alphabet;
-- Kleene star of the alphabet
-- a formal language is a set of strings in some alphabet
-- 




module STLC2 where

module STLC where
 module Syntax where
  open BaseDefinitions.BaseTypes.Nat
  data Type : Set where
   ℕ : Type
   _⇒_  : Type → Type → Type

  data Context : Set where
   ∅ : Context
   _,_ : Type → Context → Context

  data Var : Set where
   $ : Nat → Var

  data Term : Set where
   $ : Nat → Term
   zero : Term
   suc : Term
   lam : Var → Term → Term
   _·_ : Term → Term → Term

  data Judgement : Set where
   [_⊢_∈_] : Context → Term → Type → Judgement

  -- not quite, needs to be variable judgements, not just concrete judgements
  data Rule : Set where
   _/_ : Judgement →  Judgement → Rule

 {-
 module Semantics1
 -}
 {-
   proof composition based solely on types is non-deterministic due to the fact that 
   contexts are multi-sets rather than sets, unless we specify which proofs attach to which assumptions;

   composition is per assumption just like substitution is per variable

   ([Γ₁, a : A, Γ₂] B) ∘ ([ Γ₃ ] A) / a = ([Γ₁ , Γ₃ , Γ₂] B)
 -}

 {-
 data Context : Set where
  ‌∅ : Context
  _,_ : Context → Type → Context
 -} 
  -- associate variables to positions in the context list

 data Term : Set where
  zero : Term
  suc : Term
  ℕ : Term
  Type : Term
  _·_ : Term → Term → Term

 {-
 _[_/_] : Term → Fin (⌋ → Term → Term
 a [ x / b ] = 
 -}

 {-
 data _∈_ : Term → Term → Set where
  Hyp : {a A : Term} hyp ∈ [ A ] A
  ℕ-form : ℕ ∈ Type
  ℕ-intro0 : zero ∈ ([ ∅ ] ℕ)
  ℕ-intro1 : suc ∈ [ ∅ , ℕ ] ℕ
  ·-intro : {s t S T} → s ∈ S → t ∈ T → (s · t) ∈ (S · T)
 -}

 {-
 <_> : Term → Term
 < ℕ > = ℕ
 < zero > = zero
 -}
 

{-
someLemma : ∀ {i j k} {W : Set i} {_R_ : W → W → Set j} → (P : W → Set k) → (w : W) → ((¬ ([] _R_ w P)) ↔ (<> _R_ w (¬ ∘ P))) → ((x : W) → (w R x) → ¬ (¬ (P x))) → ((x : W) → (w R x) → P x)
someLemma {i} {j} {k} {W} {_R_} P w ( ¬[]P→¬[]¬¬P , ¬[]¬¬P→¬[]P ) []¬¬P = []P
 where
-}
 {-
  []¬P → ¬<>P = ¬¬[]¬P
  []¬¬P → ¬<>¬¬P = ¬¬[]¬¬¬P
  []¬¬P → ¬¬[]¬¬P
  ¬¬[]¬¬P ∧ ¬[]P→¬[]¬¬P → ¬¬[]P
  ¬¬[]P ∧ ¬[]¬¬P→¬[]P → ¬¬[]¬¬P
 -}
  -- []P

{-
~[]P = <>~P
~[]P = ~~[]~~P
[]P = ~<>~P
<>P = ~[]~P

<>~P = ~[]~~P

~[]P = <>~P


~<>P 
-}


{-
  X     It is a form of type annotation: 'Ξxy' says that 'given an x, we can get a y'.
  L     The type of types is L, so 'Lx' tells us that 'x' is a type

  K
  S

  P x y   = X(Kx)(Ky)         x → y     "cP @ x @ y encodes that x implies y."
  F x y z = Xx(S(Ky)z)        
  G x y z = Xx(Syz)
  H       = S(KL)K            x a Prop   "x is a proposition (encoded as cH @ x)"   


  Hx = S(KL)Kx = KLx(Kx) = L(Kx)


  Id   : WellTyped c -> WellTyped c

  Beta : WellTyped c 
          -> (reduce c = c') 
          -> WellTyped c'

  Pe   : WellTyped (cP @ x @ y) 
          -> WellTyped x 
          -> WellTyped y

  Pi   : (WellTyped x -> WellTyped y) 
          -> WellTyped (cH @ x) 
          -> WellTyped (cP @ x @ y)

  PH   : (WellTyped x -> WellTyped (cH @ y)) 
          -> WellTyped (cH @ x) 
          -> WellTyped (cH @ (cP @ x @ y))

  Xe   : WellTyped (cX @ x @ y) 
          -> WellTyped (x @ v)
          -> WellTyped (y @ v)

  XH   : (WellTyped (x @ a) -> WellTyped (cH @ (y @ a)))
          -> WellTyped (cL @ x)
          -> WellTyped (cH @ (cX @ x @ y))

  Fe   : WellTyped (cF @ x @ y @ z)
          -> WellTyped (x @ v)
          -> WellTyped (y @ (z @ v))

  Fi   : (WellTyped (x @ a) -> WellTyped (y @ (z @ a)))
          -> WellTyped (cL @ x)
          -> WellTyped (cF @ x @ y @ z)

  FL   : (WellTyped (x @ a) -> WellTyped (cL @ y))
          -> WellTyped (cL @ x)
          -> WellTyped (cL @ (cF @ x @ y))

  Ge   : WellTyped (cG @ x @ y @ z)
          -> WellTyped (x @ v)
          -> WellTyped (y @ v @ (z @ v))

  Gi   : (WellTyped (x @ a) -> WellTyped (y @ a @ (z @ a))
          -> WellTyped (cL @ x)
          -> WellTyped (cG @ x @ y @ z)

  GL   : (WellTyped (x @ a) -> WellTyped (cL @ (y @ a)))
          -> WellTyped (cL @ x)
          -> WellTyped (cL @ (cG @ x @ y))


  \x.\y.\p.p x y

-}
