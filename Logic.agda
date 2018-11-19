module Modality where

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
    open Reflexivity
    open Symmetry public
    open Transitivity public
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
    foldr : ∀ {i j} {A : Set i} {B : Set j} → (A → B → B) → B → List A → B
    foldr f b [] = b
    foldr f b (a ∷ as) = f a (foldr f b as)
    
    _++_ : ∀ {i} {A : Set i} → (x y : List A) → List A
    [] ++ ys = ys
    (x  ∷ xs) ++ ys = x ∷ (xs ++ ys)
   open Operations public

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
 open BaseDefinitions.BaseTypes.Bool
 module Operations where
  not : Bool → Bool
  not true = false
  not false = true
  
  _and_ : Bool → Bool → Bool
  true and x = x
  false and x = false

  _or_ : Bool → Bool → Bool
  true or x = true
  false or x = x
  

module Functions where
 open BaseDefinitions.Implication
 id : ∀ {i} {A : Set i} → A → A
 id = λ x → x
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
  open BaseDefinitions.Equality.Definition
  Associative : ∀ {i} {A : Set i} (f : A → A → A) → Set i
  Associative {i} {A} f = (x y z : A) → (f (f x y) z) ≡ (f x (f y z))

  Commutative : ∀ {i} {A : Set i} (f : A → A → A) → Set i
  Commutative {i} {A} f = (x y : A) → (f x y) ≡ (f y x)

  _isLInverseOfᵢ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set
  g isLInverseOfᵢ f = (g ∘ f) ≡ id

  _isRInverseOfᵢ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set
  g isRInverseOfᵢ f = (f ∘ g) ≡ id

  _isInverseOfᵢ_ : ∀ {i j} {A : Set i} {B : Set j} (g : B → A) (f : A → B) → Set
  g isInverseOfᵢ f = (g isLInverseOfᵢ f) ∧ (g isRInverseOfᵢ f)  

  _hasLInverseᵢ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set
  _hasLInverseᵢ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , ((g ∘ f) ≡ id)

  _hasRInverseᵢ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set
  _hasRInverseᵢ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , ((f ∘ g) ≡ id)

  _hasLInverseₑ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set
  _hasLInverseₑ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , ((x : A) , (g (f x)) ≡ x)

  _hasRInverseₑ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set
  _hasRInverseₑ {i} {j} {A} {B} f = ∃ g ∈ (B → A) , ((x : B) , (f (g x)) ≡ x)
{-
 relativized to some equivalence relation?

-}
  
  
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
 module Iteration where
  open Composition.Definition
  open BaseDefinitions.Nat
  module Definition where
   _**_ : ∀ {i} {A : Set i} → (A → A) → Nat → (A → A)
   f ** zero = λ x → x
   f ** (suc n) = f ∘ (f ** n)

  open Definition
  
 open Iteration
 

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
  
 open Relations
 module Results where
  


module BaseAbstractAlgebra where
 record Monoid {i} : Set (lsuc i) where
  field
   M : Set i
   _∘_ : M → M → M 
 record Group {i} : Set (lsuc i) where
  field
   carrier : Set i
   
   
module FunctionArithmetic where
 open BaseDefinitions.Equality.Definition
 open BaseDefinitions.Equality.Properties
 open BaseArithmetic
 open Functions
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

module Numbers where
 open BaseDefinitions.BaseTypes.Bool
 open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
 open BaseDefinitions.BaseTypes.Fin
 open BaseDefinitions.Product
 

 module Naturals where
  module PowerExpansion where
   open BaseDefinitions.BaseTypes.List
   Nat : Set
   Nat = List Bool
 module NonZeroNats where

 module Primes where
  -- fundamental theorem of arithmetic: unique decomposition into products of powers of primes
  -- nth prime function

 module Integers where
  data ℤ : Set where
   zero : ℤ
   possuc : ℕ → ℤ 
   negsuc : ℕ → ℤ
 open Integers
 -- integers satisfy unique representation under this definition;
 -- unique representation allows the equality relation of the type theory to serve
 -- as the equivalence relation on the type, so given two equivalent objects x and y,
 -- a proof of P(x) can be turned into a proof of P(y)
 -- binary representations of integers
 -- finite integers
 
 module Rationals where
  module Representations where
   module Fractions where
    data ℚ : Set where
     _/_ : ℤ → ℕ → ℚ
   module MixedFractions where
    data ℚ : Set where
     _[_/_] : ℤ → ℕ → ℕ → ℚ
   module PowerExpansions where


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

 -- translation of terminating / repeating real power expansions into Rationals

 module Algebraic where
 module Constructible where
 module Computable where
 module Complex where
  open Reals.BooleanExpansions
  ℂ : Set
  ℂ = ℝ × ℝ

 module Special where
 -- sqrt(2)
 -- e
 -- pi
 -- phi 

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

module Geometry where
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
  open BaseDefinitions.BaseTypes.List
  
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
 Cell automata
 Pushdown automata
 Primitive recursive functions
 Nondeterministic finite state automaton
 Deterministic finite state machine
 subleq
 x86
 Arithmetical definability of general recursive functions
 -}
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

  -- while that fixes the problems of the previous example, it's still a bit too specific
  -- ideally we would encompass everything that can reasonably satisfy the queue automaton conditions
  -- so we should probably assume that our alphabets can be any finite sets with a decidable equality
  -- relation defined on them; it should probably be a member of Set as well, just for good measure.
  -- let's abstract this over the universe hierarchy while we're at it:
  -- as you can see in the Cardinality module though there are many different ways to formulate the notion of
  -- finiteness, infiniteness, cardinality etc..
  -- similarly we may want to adjust what we mean when we say that the set has decidable equality
  -- so let's abstract over that as well
  module QueueAutomaton3 where
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
