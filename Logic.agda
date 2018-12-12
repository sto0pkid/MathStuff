module Logic where

open import Agda.Primitive



module BaseDefinitions where
 module Levels where
  record Lift {i} {j} (A : Set i) : Set (i ⊔ j) where
   field
    lower : A
    
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

  



 module Equality where
  module Definition where
   open Negation.Definition
   data _≡_ {i} {A : Set i} (x : A) : A → Set i where
    refl : x ≡ x

   _≠_ : ∀ {i} {A : Set i} (x : A) → A → Set i
   x ≠ y = ¬ (x ≡ y)

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
   {-# BUILTIN BOOL  Bool  #-}
   {-# BUILTIN TRUE  true  #-}
   {-# BUILTIN FALSE false #-}
   

  module Nat where
   data Nat : Set where
    zero : Nat
    suc : Nat → Nat

   {-# BUILTIN NATURAL Nat #-}

  module List where
   data List {i} (A : Set i) : Set i where
    [] : List A
    _∷_ : A → List A → List A
   {-# BUILTIN LIST List #-}
   infixr 0 _∷_

  module Char where
   postulate Char : Set
   {-# BUILTIN CHAR Char #-}
   
  module String where
   postulate String : Set
   {-# BUILTIN STRING String #-}
  
  module CharBindings where
   open Char
   open Nat
   open Bool
   open String
   primitive
    primIsLower    : Char → Bool
    primIsDigit    : Char → Bool
    primIsAlpha    : Char → Bool
    primIsSpace    : Char → Bool
    primIsAscii    : Char → Bool
    primIsLatin1   : Char → Bool
    primIsPrint    : Char → Bool
    primIsHexDigit : Char → Bool
    primToUpper    : Char → Char
    primToLower    : Char → Char
    primCharToNat  : Char → Nat
    primNatToChar  : Nat → Char
    primShowChar   : Char → String
    
  module StringBindings where
   open String
   open Char
   open List
   open Bool
   postulate primStringToList   : String → List Char
   postulate primStringFromList : List Char → String
   postulate primStringAppend   : String → String → String
   postulate primStringEquality : String → String → Bool
   postulate primShowString     : String → String
 

  module Fin where
   open Nat renaming (Nat to ℕ)
   module Definition where
    data Fin : ℕ → Set where
     zero : {n : ℕ} → Fin (suc n)
     suc : {n : ℕ} → Fin n → Fin (suc n)
   open Definition public
    
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

 ∨-map : ∀ {i j k l} {A : Set i} {A' : Set j} {B : Set k} {B' : Set l} → (A → A') → (B → B') → A ∨ B → A' ∨ B'
 ∨-map f g (inl a) = inl (f a)
 ∨-map f g (inr b) = inr (g b)


module Relations where
  -- unary relations are sets, covered in the Sets module
  -- N-ary relations depend on Nats
  -- indexing the arguments to a relation by something more general than Nat?
  -- index by a tree you get a pattern?
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

    module Totality where
     open BaseDefinitions.Sum
     Total : ∀ {i j} → {A : Set i} → Rel₂ {i} {j} A → Set (i ⊔ j)
     Total {i} {j} {A} R = (x y : A) → (R x y) ∨ (R y x)

    open Reflexivity public
    open Symmetry public
    open Transitivity public
    open Totality
    
    record Equivalence {i} {j} {A : Set i} (R : A → A → Set j) : Set (i ⊔ j) where
     field
      reflexive : Reflexive R
      symmetric : Symmetric R
      transitive : Transitive R

    -- antisymmetry is inherently more complex than:
      -- reflexivity
      -- symmetry
      -- transitivity
      -- equivalences
    -- even needs to be defined relative to an equivalence relation:
    module Antisymmetry where
     Antisymmetric : ∀ { i j k} → {A : Set i} → (_~_ : A → A → Set k) → Equivalence _~_ → Rel₂ {i} {j} A → Set ((i ⊔ j) ⊔ k)
     Antisymmetric {i} {j} {k} {A} _~_ ~-equiv R = {x y : A} → R x y → R y x → x ~ y
    module Asymmetry where
     open BaseDefinitions.Void     
     Asymmetric : ∀ {i j} {A : Set i} (R : A → A → Set j) → Set (i ⊔ j)
     Asymmetric {i} {j} {A} R = {x y : A} → R x y → R y x → ⊥

    module Irreflexivity where
     open BaseDefinitions.Negation.Definition
     Irreflexive : ∀ {i j} {A : Set i} (R : A → A → Set j) → Set (i ⊔ j)
     Irreflexive {i} {j} {A} R = {x : A} → ¬ (R x x)
   open Properties public
  open BinaryRelations public

module Equality where
  module Properties where
   open BaseDefinitions.Void
   open BaseDefinitions.Unit
   open BaseDefinitions.Equality.Definition
   open Relations
   [A≡B]→[A→B] : ∀ {i} {A B : Set i} → A ≡ B → A → B
   [A≡B]→[A→B] refl a = a

   ⊤≠⊥ : ⊤ ≠ ⊥
   ⊤≠⊥ ⊤=⊥ = [A≡B]→[A→B] ⊤=⊥ unit

   ≡-sym : ∀ {i} {A : Set i} → Symmetric (_≡_ {i} {A})
   ≡-sym refl = refl

   ≡-trans : ∀ {i} {A : Set i} → Transitive (_≡_ {i} {A})
   ≡-trans refl refl = refl

   cong : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → {x y : A} → x ≡ y → (f x) ≡ (f y)
   cong f refl = refl

   transport : ∀ {i j} {A : Set i} → (P : A → Set j) → {x y : A} → x ≡ y → P x  → P y
   transport P refl Px = Px

   coerce : ∀ {i} {A B : Set i} → A → A ≡ B → B
   coerce {i} {A} {.A} a refl = a

   ≡-equiv : ∀ {i} {A : Set i} → Equivalence {i} {i} {A} _≡_
   ≡-equiv =
    record {
     reflexive = λ x → refl ;
     symmetric = ≡-sym ;
     transitive = ≡-trans 
    }

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

  _eq_ : Bool → Bool → Bool
  true eq true = true
  true eq false = false
  false eq true = false
  false eq false = true

  BoolEq : Bool → Bool → Bool
  BoolEq true  true  = true
  BoolEq true  false = false
  BoolEq false true  = false
  BoolEq false false = true

  -- x ≤ y is the same as x → y
  Bool≤ : Bool → Bool → Bool
  Bool≤ true true = true
  Bool≤ true false = false
  Bool≤ false true = true
  Bool≤ false false = true

  -- x < y is the same as ¬ (y → x)
  Bool< : Bool → Bool → Bool
  Bool< true true = false
  Bool< true false = false
  Bool< false true = true
  Bool< false false = false

  if_then_else_ : ∀ {i} {A : Set i} → Bool → A → A → A
  if true then a else b = a
  if false then a else b = b

  -- induction principle for Bool
  Bool-ind : ∀ {i} {A : Bool → Set i} → A true → A false → (b : Bool) → A b
  Bool-ind t f true  = t
  Bool-ind t f false = f
 
 module Complex where
  open BaseDefinitions.Equality.Definition
  open BaseDefinitions.Product
  halfAdd : Bool → Bool → Bool × Bool
  halfAdd true  true  = false , true
  halfAdd true  false = true  , false
  halfAdd false true  = true  , false
  halfAdd false false = false , false

  fullAdd : Bool → Bool → Bool → Bool × Bool
  fullAdd true  true  true  = true  , true
  fullAdd true  true  false = false , true
  fullAdd true  false true  = false , true
  fullAdd true  false false = true  , false
  fullAdd false true  true  = false , true
  fullAdd false true  false = true  , false
  fullAdd false false true  = true  , false
  fullAdd false false false = false , false

  dite : ∀ {i} {A : Set i} → (b : Bool) → ((b ≡ true) → A) → ((b ≡ false) → A) → A
  dite true  t f = t refl
  dite false t f = f refl

  dite-ind : ∀ {i} {P : Bool → Set i} → (b : Bool) → ((b ≡ true) → P true) → ((b ≡ false) → P false) → P b
  dite-ind true  t f = t refl
  dite-ind false t f = f refl

 module Conversions where
  open BaseDefinitions.Nat
  boolToNat : Bool → Nat
  boolToNat true  = 1
  boolToNat false = 0

 -- functional completeness
 -- reversibility

 module Predicates where
  open BaseDefinitions.Void
  open BaseDefinitions.Unit
  isTrue : Bool → Set
  isTrue true = ⊤
  isTrue false = ⊥


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
 module Maybe where
  module Definition where
   data Maybe {i} (A : Set i) : Set i where
    Nothing : Maybe A
    Just : A → Maybe A
  module Operations where
   open Definition
   MaybeMap : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → Maybe A → Maybe B
   MaybeMap f Nothing = Nothing
   MaybeMap f (Just x) = Just (f x)

  module BooleanPredicates where
   open Definition
   open BaseDefinitions.Bool
   checkMaybe : ∀ {i} {A : Set i} → Maybe A → Bool
   checkMaybe Nothing = false
   checkMaybe (Just x) = true

  module Complex where
   open Definition
   open BaseDefinitions.Bool
   open BaseDefinitions.Equality.Definition
   open BooleanPredicates
   
   extractMaybe : ∀ {i} {A : Set i} → (m : Maybe A) → (checkMaybe m) ≡ true → A
   extractMaybe {A} Nothing ()
   extractMaybe {A} (Just x) p = x


 module List where
   open BaseDefinitions.List
   module Operations where
    open BaseDefinitions.Nat renaming (Nat to ℕ)
    open BaseDefinitions.Fin
    
    foldr : ∀ {i j} {A : Set i} {B : Set j} → (A → B → B) → B → List A → B
    foldr f b [] = b
    foldr f b (a ∷ as) = f a (foldr f b as)

    map : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → List A → List B
    map f [] = []
    map f (a ∷ as) = (f a) ∷ (map f as)

    [_] : ∀ {i} {A : Set i} → A  → List A
    [ x ] = x ∷ []

    length : ∀ {i} {A : Set i} → List A → ℕ
    length [] = 0
    length (a ∷ as) = suc (length as)

    _<_> : ∀ {i} {A : Set i} → (l : List A) → Fin (length l) → A
    [] < () > 
    (a ∷ as) < zero > = a
    (a ∷ as) < (suc n) > = as < n >

    _++_ : ∀ {i} {A : Set i} → (x y : List A) → List A
    [] ++ ys = ys
    (x  ∷ xs) ++ ys = x ∷ (xs ++ ys)

    rev : ∀ {i} {A : Set i} → List A → List A
    rev [] = []
    rev (x ∷ xs) = (rev xs) ++ (x ∷ [])
   open Operations public
   module Predicates where
   {-
    _∈_ : ∀ {i} {A : Set i} → A → List A → Set i
    x ∈ L = 
  -}
   module BooleanPredicates where
    open BaseDefinitions.Bool
    open Boolean.Operations
    find  : ∀ {i} {A : Set i} → A → List A → (A → A → Bool) → Bool
    find x [] f = false
    find x (y ∷ ys) f = if (f x y) then true else (find x ys f)    

    ListEq : {A : Set} (eq : A → A → Bool) (x y : List A) → Bool
    ListEq eq [] [] = true
    ListEq eq (a₁ ∷ as₁) [] = false
    ListEq eq [] (a₂ ∷ as₂) = false
    ListEq eq (a₁ ∷ as₁) (a₂ ∷ as₂) = if (eq a₁ a₂) then ((ListEq eq) as₁ as₂) else false
    
 module Vector where
  open BaseDefinitions.Nat
  open BaseDefinitions.Vector
  module BooleanPredicates where
   open BaseDefinitions.Bool
   open Boolean.Operations
   open BaseDefinitions.Fin
   VectorEq : {A : Set} {n : Nat} → (eq : A → A → Bool) → (x y : Vector A n) → Bool 
   VectorEq eq [] [] = true
   VectorEq eq (a₁ ∷ as₁) (a₂ ∷ as₂) = if (eq a₁ a₂) then ((VectorEq eq) as₁ as₂) else false

   [_] : ∀ {i} {A : Set i} → A → Vector A 1
   [ a ] = a ∷ []

   _<_> : ∀ {i} {A : Set i} {n : Nat} → Vector A n → Fin n → A
   [] < () >
   (a ∷ as) < zero > = a
   (a ∷ as) < suc n > = as < n >   

 module BinTree where
  open BaseDefinitions.Bool
  open BaseDefinitions.Nat
  open BaseDefinitions.Vector
  data BinTree (A : Set) : Nat → Set where
   leaf : A → BinTree A 0
   node : {n : Nat} → BinTree A n → BinTree A n → BinTree A (suc n)

  store : {A : Set} {n : Nat} → BinTree A n → A → Vector Bool n → BinTree A n
  store {A} {0} (leaf a) x [] = leaf x
  store {A} {(suc n)} (node a b) x (true ∷ rest) = node (store a x rest) b
  store {A} {(suc n)} (node a b) x (false ∷ rest) = node a (store b x rest)

  retrieve : {A : Set} {n : Nat} → BinTree A n → Vector Bool n → A
  retrieve {A} {0} (leaf a) [] = a
  retrieve {A} {(suc n)} (node a b) (true ∷ rest) = retrieve a rest
  retrieve {A} {(suc n)} (node a b) (false ∷ rest) = retrieve b rest


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
  open Relations.BinaryRelations.Properties.Reflexivity
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

 -- could be relativized to equivalence relations
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

  _hasInjectionTo_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A hasInjectionTo B = ∃ f ∈ (A → B) , (f isInjective)

  Surjective : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  Surjective {i} {j} {A} {B} f = (y : B) → ∃ x ∈ A , (f x ≡ y)

  _isSurjection : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  _isSurjection = Surjective

  _isSurjective : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  _isSurjective = Surjective

  _hasSurjectionTo_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A hasSurjectionTo B = ∃ f ∈ (A → B) , (f isSurjective)

  Bijective : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  Bijective f = (f isInjective) ∧ (f isSurjective)

  _isBijection : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  _isBijection = Bijective

  _isBijective : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
  _isBijective = Bijective

  _hasBijectionTo_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A hasBijectionTo B = ∃ f ∈ (A → B) , (f isBijective)

  _hasBijectionWith_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  _hasBijectionWith_ = _hasBijectionTo_
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
  

 -- could be relativized to equivalence relations defined on the sets
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

   Rinvₑ-lemma : ∀ {i j} {A : Set i} {B : Set j} → {f : A → B} → {g : B → A} → f isRInverseOfₑ g → g isLInverseOfₑ f
   Rinvₑ-lemma f-rinv a = f-rinv a

   Linvₑ-lemma : ∀ {i j} {A : Set i} {B : Set j} → {f : A → B} → {g : B → A} → f isLInverseOfₑ g → g isRInverseOfₑ f
   Linvₑ-lemma f-linv b = f-linv b 

   Rinvᵢ-lemma : ∀ {i j} {A : Set i} {B : Set j} → {f : A → B} → {g : B → A} → f isRInverseOfᵢ g → g isLInverseOfᵢ f
   Rinvᵢ-lemma f-rinv = f-rinv

   Linvᵢ-lemma : ∀ {i j} {A : Set i} {B : Set j} → {f : A → B} → {g : B → A} → f isLInverseOfᵢ g → g isRInverseOfᵢ f
   Linvᵢ-lemma f-linv = f-linv

    
   invₑ-sym : ∀ {i j} {A : Set i} {B : Set j} → {f : A → B} → {g : B → A} → f isInverseOfₑ g → g isInverseOfₑ f
   invₑ-sym {f = f} {g = g} (l , r) = (Rinvₑ-lemma {f = f} {g = g} r) , (Linvₑ-lemma {f = f} {g = g} l)

   invᵢ-sym : ∀ {i j} {A : Set i} {B : Set j} → {f : A → B} → {g : B → A} → f isInverseOfᵢ g → g isInverseOfᵢ f
   invᵢ-sym {f = f} {g = g} (l , r) = (Rinvᵢ-lemma {f = f} {g = g} r) , (Linvᵢ-lemma {f = f} {g = g} l)


  open FunctionInverses
  module ObjectInverses where
   -- not meaningful to talk about true "inverses" without an identity element already known
   -- identity is more basic than inverse.
   -- object inverses more basic than function inverses or function inverses more basic than object inverses or neither?
   -- functions generalize the situation; morphisms between objects
   -- translation of abstract algebra into category theory: objects become morphisms, some operation becomes composition of morphisms
   -- binary operation
   -- with an equivalence relation
   -- presumably the binary operation should be congruent with the equivalence relation
   -- and it must have an identity element
   -- equivalence relations equivalent to groupoids?
   -- use transitivity requirement to get composition of components of the relation
   -- use symmetry to get inverses
   -- use reflexivity to get identity elements
   -- and vice-versa

   {-
   _isRight_InverseOf_wrt_with-id_ : ∀ {i j} {A : Set i} → A → (A → A → A) → A → (A → A → Set j) → A → Set j
   x isRight f InverseOf y wrt _~_ with-id e = (f y x) ~ e

   _isLeft_InverseOf_wrt_with-id_ : ∀ {i j} {A : Set i} → A → (A → A → A) → A → (A → A → Set j) → A → Set j 
   x isLeft f InverseOf y wrt _~_ with-id e = (f x y) ~ e
   -}

 -- could be relativized to equivalence relations
 open Inverses
      
 module Injections where
  open BaseDefinitions.Void
  open BaseDefinitions.Equality.Definition
  open BaseDefinitions.Product
  open Special
  open Predicates
  id-inj : ∀ {i} {A : Set  i} → (id {i} {A}) isInjective
  id-inj {i} {A} {x} {y} idx≡idy = idx≡idy

  Inj-refl : ∀ {i} (A : Set i) → A hasInjectionTo A
  Inj-refl A = (id , id-inj)
  
  Inj-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → A hasInjectionTo B → B hasInjectionTo C → A hasInjectionTo C
  Inj-trans (f , f-inj) (g , g-inj) = ((g ∘ f) , (λ gfx=gfy → f-inj (g-inj gfx=gfy)))

  Inj-refl-id : ∀ {i} {A B : Set i} (AB : A  hasInjectionTo B) → ((Inj-trans (Inj-refl A) AB) ≡ AB) ∧ ((Inj-trans AB (Inj-refl B)) ≡ AB)
  Inj-refl-id {i} {A} {B} (AB , AB-inj) = refl , refl


  Inj-trans-assoc :
   ∀ {i}
   {A B C D : Set i}
   (AB : A hasInjectionTo B)
   (BC : B hasInjectionTo C)
   (CD : C hasInjectionTo D) →
   (Inj-trans AB (Inj-trans BC CD)) ≡ (Inj-trans (Inj-trans AB BC) CD)
  Inj-trans-assoc
   {i} {A} {B} {C} {D}
   (AB , AB-inj) (BC , BC-inj) (CD , CD-inj) = refl

  

  ⊥→A-inj : ∀ {i} (A : Set i) → ⊥ hasInjectionTo A
  ⊥→A-inj A = (explode , explode-inj)
   where
    explode : ⊥ → A
    explode ()

    explode-inj : explode isInjective
    explode-inj {x = ()}

  -- anti-symmetric relative to what equivalence relation?
  -- 

  -- so it's at least a preorder at any set-level
 module Surjections where
  open BaseDefinitions.Levels
  open BaseDefinitions.Equality.Definition
  open Equality.Properties
  open BaseDefinitions.Product
  open BaseDefinitions.BaseTypes.Unit
  open BaseDefinitions.Void
  open BaseDefinitions.Negation.Definition
  open Special
  open Predicates

  id-surj : ∀ {i} {A : Set i} → (id {i} {A}) isSurjective
  id-surj {i} {A} y = (y , refl)

  Surj-refl : ∀ {i} (A : Set i) → A hasSurjectionTo A
  Surj-refl {i} A = (id , id-surj)


  
  Surj-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → A hasSurjectionTo B → B hasSurjectionTo C → A hasSurjectionTo C
  Surj-trans {A = A} {B = B} {C = C} (f , f-surj) (g , g-surj) = ((g ∘ f) , g∘f-surj)
   where
    g∘f-surj : (z : C) → ∃ x ∈ A , (((g ∘ f) x) ≡ z)
    g∘f-surj z = (x , gfx=z)
     where
      y : B
      y = π₁ (g-surj z)

      gy=z : (g y) ≡ z
      gy=z = π₂ (g-surj z)
      
      x : A
      x = π₁ (f-surj y)

      fx=y : (f x) ≡ y
      fx=y = π₂ (f-surj y)
      
      gfx=z = ≡-trans (cong g fx=y) gy=z

   {-
  Surj-refl-id : ∀ {i} {A B : Set i} (AB : A  hasSurjectionTo B) → ((Surj-trans (Surj-refl A) AB) ≡ AB) ∧ ((Surj-trans AB (Surj-refl B)) ≡ AB)
  Surj-refl-id {i} {A} {B} (AB , AB-surj) = refl , refl


  Surj-trans-assoc :
   ∀ {i}
   {A B C D : Set i}
   (AB : A hasSurjectionTo B)
   (BC : B hasSurjectionTo C)
   (CD : C hasSurjectionTo D) →
   (Surj-trans AB (Surj-trans BC CD)) ≡ (Surj-trans (Surj-trans AB BC) CD)
  Surj-trans-assoc
   {i} {A} {B} {C} {D}
   (AB , AB-inj) (BC , BC-inj) (CD , CD-inj) = refl
  -}

  -- Surj-antisym
  -- relative to what equivalence relation?

  -- can't relate "A hasSurjectionTo B" to "| A | ≥ | B |"
  -- No surjection from inhabited sets to the empty set, so
  -- inhabited sets aren't "greater than" the empty set by this
  -- measure.
  ¬[⊥-terminal] : ∀ {i} → ¬ ((A : Set i) → A → ⊥)
  ¬[⊥-terminal] {i} f = f (Lift {lzero} {i} ⊤) (record{lower = unit})

  -- for every inhabited set A, surjection from A → Unit
  -- so for every inhabited set A, |A| ≥ 1
  ⊤-semiterminal : ∀ {i} {A : Set i} → A → A hasSurjectionTo ⊤
  ⊤-semiterminal a = ((λ x → unit) , (λ {unit → (a , refl)}))

  ⊥-absorb  : ∀ {i} {A : Set i} → ¬ A → A hasSurjectionTo ⊥
  ⊥-absorb {i} {A} ¬A = (¬A , λ ())
      
 module Bijections where
  open BaseDefinitions.Levels
  open BaseDefinitions.Equality.Definition
  open Equality.Properties
  open BaseDefinitions.Product
  open BaseDefinitions.BaseTypes.Unit
  open BaseDefinitions.Void
  open BaseDefinitions.Negation.Definition
  open Relations
  open Special
  open Predicates
  open Injections
  open Surjections
  open FunctionInverses

  id-bij : ∀ {i} {A : Set i} → id {i} {A} isBijection
  id-bij {i} {A} = (id-inj , id-surj)

  Bij-refl : ∀ {i} (A : Set i) → A hasBijectionWith A
  Bij-refl {i} A = (id , id-bij)

  Bij-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → A hasBijectionWith B → B hasBijectionWith C → A hasBijectionWith C
  Bij-trans {i} {j} {k} {A} {B} {C} (f , (f-inj , f-surj)) (g , (g-inj , g-surj)) = ((g ∘ f) , (g∘f-inj , g∘f-surj))
   where
    g∘f-inj = π₂ (Inj-trans (f , f-inj) (g , g-inj))
    g∘f-surj = π₂ (Surj-trans (f , f-surj) (g , g-surj))

  Bij-inv : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → f isBijective → f hasInverseₑ
  Bij-inv {i} {j} {A} {B} f (f-inj , f-surj) = g , (gf-inv , fg-inv)
   where
    g : B → A
    g b = π₁ (f-surj b)

    fg-inv : (y : B) → f (g y) ≡ y
    fg-inv y = π₂ (f-surj y)
    
    gf-inv : (x : A) → (g (f x)) ≡ x
    gf-inv x = gfx=x
     where
      x' = π₁ (f-surj (f x))
      
      fx'=fx : (f x') ≡ (f x)
      fx'=fx = π₂ (f-surj (f x))

      x'=x : x' ≡ x
      x'=x = f-inj fx'=fx

      gfx=x' : g (f x) ≡ x'
      gfx=x' = refl

      gfx=x = ≡-trans gfx=x' x'=x
      
  Inv-bij : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → (f-inv : f hasInverseₑ) → (f isBijective) ∧ ((π₁ f-inv) isBijective)
  Inv-bij {i} {j} {A} {B} f (g , (g-Linv , g-Rinv)) = ((f-inj , f-surj) , (g-inj , g-surj))
   where
    f-inj : {x y : A} → (f x) ≡ (f y) → x ≡ y
    f-inj {x} {y} fx=fy = x=y
     where
      gfx=gfy = cong g fx=fy
      x=y = ≡-trans (≡-sym (g-Linv x)) (≡-trans gfx=gfy (g-Linv y))
      
    f-surj : (y : B) → ∃ x ∈ A , ((f x) ≡ y)
    f-surj y = ((g y) , g-Rinv y)

    g-inj : {x y : B} → (g x) ≡ (g y) → x ≡ y
    g-inj {x} {y} gx=gy = ≡-trans (≡-sym (g-Rinv x)) (≡-trans (cong f gx=gy) (g-Rinv y))
      
    g-surj : (y : A) → ∃ x ∈ B , ((g x) ≡ y)
    g-surj y = ((f y) , g-Linv y)

  

  -- inversion the proper thing to use for defining antisymmetry of injections / surjections since it's the thing that provides symmetry for bijections
  -- inversion is also what gives the inverses for defining groupoids
  Bij-symm : ∀ {i j} {A : Set i} {B : Set j} → A hasBijectionWith B → B hasBijectionWith A
  Bij-symm {i} {j} {A} {B} (f , f-bij) = (π₁ (Bij-inv f f-bij)) , (second (Inv-bij f (Bij-inv f f-bij)))
  
  Bij-equiv : ∀ {i} → Equivalence (_hasBijectionWith_ {i} {i})
  Bij-equiv {i} =
   record {
    reflexive = Bij-refl {i} ;
    symmetric = Bij-symm {i} {i} ;
    transitive = Bij-trans {i} {i} {i}
   }

  _hasBijection₂With_ : ∀ {i} {j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A hasBijection₂With B = ∃ f ∈ (A → B) , (f hasInverseᵢ)

  Bij₂-refl : ∀ {i} (A : Set i) → A hasBijection₂With A
  Bij₂-refl {i} A = (id , (id , (refl , refl)))

  {-
   ∘-assoc :
    ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
    → (f : A → B) → (g : B → C) → (h : C → D)
    → ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f)) 
   ∘-assoc f g h = refl
  -}

  Bij₂-trans : ∀ {i} {A B C : Set i} → A hasBijection₂With B → B hasBijection₂With C → A hasBijection₂With C
  Bij₂-trans
   {i} {A} {B} {C}
   (AB , (BA , (BAL , BAR)))
   (BC , (CB , (CBL , CBR))) =
   ((BC ∘ AB) , ((BA ∘ CB) , (((≡-trans ∘ (cong₂ BA AB)) CBL BAL) , ((≡-trans ∘ (cong₂ BC CB)) BAR CBR))))
   where
    open Composition.Properties
    cong₂ :
     ∀ {i} {j} {A : Set i} {B : Set j} →
     (xy : A → B)
     (yx : B → A)
     {q r : A → A} →
     (q ≡ r) →
     (xy ∘ (q ∘ yx)) ≡ (xy ∘ (r ∘ yx))
    cong₂ xy yx = cong (λ q → xy ∘ (q ∘ yx))
  
  {-
  Bij₂-refl-id :
   ∀ {i} {A B : Set i}
   (AB : A  hasBijection₂With B) →
   ((Bij₂-trans (Bij₂-refl A) AB) ≡ AB) ∧ ((Bij₂-trans AB (Bij₂-refl B)) ≡ AB)
  Bij₂-refl-id
   {i} {A} {B}
   (AB , (BA , (BA-Linv , BA-Rinv))) = (proof1 , proof2)
   where
    cong₂ :
     ∀ {i} {j} {A : Set i} {B : Set j} →
     (xy : A → B)
     (yx : B → A)
     {q r : A → A} →
     (q ≡ r) →
     (xy ∘ (q ∘ yx)) ≡ (xy ∘ (r ∘ yx))
    cong₂ xy yx = cong (λ q → xy ∘ (q ∘ yx))

    cong₂-id-id=cong-id : cong₂ id id ≡ cong id
    cong₂-id-id=cong-id = refl
  
    AB* = (AB , (BA , (BA-Linv , BA-Rinv)))
    
    A* : A hasBijection₂With A
    A* = Bij₂-refl A

    A*-lemma : A* ≡ (id , (id , (refl , refl)))
    A*-lemma = refl

    p-lemma : ∀ {i} {A : Set i} {x : A} → (p : x ≡ x) → (p ≡ refl)
    p-lemma {i} {A} {x} refl = refl

    A*-lemma3 : (first (π₂ (π₂ (Bij₂-trans (Bij₂-refl A) AB*)))) ≡ ((≡-trans ∘ (cong₂ id id)) BA-Linv refl)
    A*-lemma3 = refl

    {-
    A*-lemma9 : (first (π₂ (π₂ (Bij₂-trans (Bij₂-refl A) AB*)))) ≡ (λ q → refl)
    A*-lemma9 = p-lemma (first (π₂ (π₂ (Bij₂-trans (Bij₂-refl A) AB*))))
    -}

    A*-lemma4 : ((≡-trans ∘ (cong₂ id id)) BA-Linv refl) ≡ ((≡-trans ∘ (cong id)) BA-Linv refl)
    A*-lemma4 = refl

    cong-id-lemma : ∀ {i} {A : Set i} {x y : A} → (p : x ≡ y) → ((cong id p) ≡ p)
    cong-id-lemma {i} {A} {x} {.x} refl = refl

    A*-lemma5 : ((≡-trans ∘ (cong id)) BA-Linv refl) ≡ (≡-trans (cong id BA-Linv) refl)
    A*-lemma5 = refl
    -- A*-lemma6 : (≡-trans ((cong id) BA-Linv) refl) ≡ 

    
    A*-lemma6 : (≡-trans ((cong id) BA-Linv) refl) ≡ (≡-trans BA-Linv refl)
    A*-lemma6 = cong (λ q → ≡-trans q refl) (cong-id-lemma BA-Linv)

    {-
    A*-lemma7 : (≡-trans BA-Linv refl) ≡ BA-Linv
    A*-lemma7 = 
    -}

    {-
    A*-lemma2 : ((≡-trans ∘ (cong₂ id id)) BA-Linv refl) ≡ BA-Linv
    A*-lemma2 = refl
    -}

    {-
    lemma1 : (Bij₂-trans (id , (id , (refl , refl))) AB*) ≡ ((AB ∘ id) , ((id ∘ BA) , ((≡-trans (cong (λ q x → id (q x)) (cong (λ q x → q (id x)) BA-Linv)) refl) , (≡-trans (cong (λ q x → id (q x)) (cong (λ q x → q (id x)) BA-Rinv)) refl))))
    lemma1 = refl
    -}
    
    proof1 {-: (Bij₂-trans (id , (id , (refl , refl))) AB*) ≡ AB*
    proof1 = refl
    -}
    proof2
  -}

module LogicFunctionProperties where
 open BaseDefinitions.Product
 open BaseDefinitions.Equality.Definition
 open Equality.Properties
 open BaseDefinitions.Sum
 open Functions.Predicates
 
 mkPair : {A B : Set} → A → B → A ∧ B
 mkPair a b = a , b

 mkExists : {A : Set} {B : A → Set} → (a : A) → B a → ∃ x ∈ A , (B x)
 mkExists a b = a , b

 ∧-≡-lemma : {A B : Set} → {a a' : A} → {b b' : B} → a ≡ a' → b ≡ b' → (mkPair a b) ≡ (mkPair a' b')
 ∧-≡-lemma refl refl = refl

 ∧-bijection-lemma : {A B A' B' : Set} → (A hasBijectionWith A') → (B hasBijectionWith B') → (A ∧ B) hasBijectionWith (A' ∧ B')
 ∧-bijection-lemma {A} {B} {A'} {B'} (f , (f-inj , f-surj)) (g , (g-inj , g-surj)) = (h , (h-inj , h-surj))
  where
   h : (A ∧ B) → (A' ∧ B')
   h (a , b) = (f a) , (g b)

   h-inj : h isInjection
   h-inj {(a₁ , b₁)} {(a₂ , b₂)} p = ∧-≡-lemma (f-inj (cong first p)) (g-inj (cong second p))

      
   h-surj : h isSurjection
   h-surj (a' , b') = ((π₁ (f-surj a')) , (π₁ (g-surj b'))) , (∧-≡-lemma (π₂ (f-surj a')) (π₂ (g-surj b')))


 injLeft : ∀ {i j} {A : Set i} {B : Set j} → A → A ∨ B
 injLeft {i} {j} {A} {B} a = inl a

 injRight : ∀ {i j} {A : Set i} {B : Set j} → B → A ∨ B
 injRight {i} {j} {A} {B} b = inr b
 

    
 inl-injHelper : {A B : Set} {p q : A ∨ B} → p ≡ q → (s : ∃ a ∈ A , (p ≡ (inl a))) → (t : ∃ a' ∈ A , (q ≡ (inl a'))) → (π₁ s)  ≡ (π₁ t)
 inl-injHelper {A} {B} {p} {.p} refl (a , refl) (a' , refl) = refl

 inr-injHelper : {A B : Set} {p q : A ∨ B} → p ≡ q → (s : ∃ b ∈ B , (p ≡ (inr b))) → (t : ∃ b' ∈ B , (q ≡ (inr b'))) → (π₁ s) ≡ (π₁ t)
 inr-injHelper {A} {B} {p} {.p} refl (b , refl) (b' , refl) = refl

    
 inl-inj : {A B : Set} → (injLeft {lzero} {lzero} {A} {B}) isInjective
 inl-inj {A} {B} {a} {a'} p = inl-injHelper p (a , refl) (a' , refl)

 inr-inj : {A B : Set} → (injRight {lzero} {lzero} {A} {B}) isInjective
 inr-inj {A} {B} {b} {b'} p = inr-injHelper p (b , refl) (b' , refl)
 
    
 ∨-bijection-lemma : {A B A' B' : Set} → (A hasBijectionWith A') → (B hasBijectionWith B') → (A ∨ B) hasBijectionWith (A' ∨ B')
 ∨-bijection-lemma {A} {B} {A'} {B'} (f , (f-inj , f-surj)) (g , (g-inj , g-surj)) = (h , (h-inj , h-surj))
  where
   h : (A ∨ B) → (A' ∨ B')
   h (inl a) = inl (f a)
   h (inr b) = inr (g b)

   h-inj : h isInjection
   h-inj {inl a₁} {inl a₂} p = cong inl (f-inj (inl-inj p))
   h-inj {inl a₁} {inr b₂} ()
   h-inj {inr b₁} {inl a₂} ()
   h-inj {inr b₁} {inr b₂} p = cong inr (g-inj (inr-inj p))
      
   h-surj : h isSurjection
   h-surj (inl a') = inl (π₁ (f-surj a')) , cong inl (π₂ (f-surj a'))
   h-surj (inr b') = inr (π₁ (g-surj b')) , cong inr (π₂ (g-surj b'))
   
module BaseArithmetic where
 open BaseDefinitions.BaseTypes.Nat public renaming (Nat to ℕ)
 module Operations where
  open BaseDefinitions.Product
  open Containers.Maybe.Definition
  open Containers.Maybe.Operations
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

  diff : ℕ → ℕ → ℕ
  diff 0       0       = 0
  diff 0       (suc y) = (suc y)
  diff (suc x) 0       = (suc x)
  diff (suc x) (suc y) = diff x y

  -- can this be made cleaner?
  div-helper : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ
  div-helper 0       n (d , zero)          = ((suc d) , 0)
  div-helper 0       n (d , (suc r))       = (d , (n - r))
  div-helper (suc x) n (d , zero)          = div-helper x n ((suc d) , n)
  div-helper (suc x) n (d , (suc r))       = div-helper x n (d , r)
 
  _÷_ : ℕ → ℕ → Maybe (ℕ × ℕ)
  (x ÷ 0)       = Nothing
  (0 ÷ (suc n)) = Just (0 , 0)
  ((suc x) ÷ (suc n)) = Just (div-helper x n (0 , n))

  _div_ : ℕ → ℕ → Maybe ℕ
  x div y = MaybeMap first (x ÷ y)
 
  _mod_ : ℕ → ℕ → Maybe ℕ
  x mod y = MaybeMap second (x ÷ y)

  {-
  log-base_of_ : ℕ → ℕ → Maybe (ℕ × ℕ)
  log-base 0 of x = Nothing
  log-base (suc n) of x = 
  -}

 module FinOperations where
  open BaseDefinitions.Product
  open BaseDefinitions.Fin
  open Containers.Maybe.Definition

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

  n→Fin[n+1] : (n : ℕ) → Fin (suc n)
  n→Fin[n+1] 0 = zero
  n→Fin[n+1] (suc n) = suc (n→Fin[n+1] n)
 
  Fin[n]→Fin[n+1] : {n : ℕ} → Fin n → Fin (suc n)
  Fin[n]→Fin[n+1] {0} ()
  Fin[n]→Fin[n+1] {suc n} zero = zero
  Fin[n]→Fin[n+1] {suc n} (suc m) = suc (Fin[n]→Fin[n+1] m)

  Fin→Nat : {n : ℕ} → Fin n → ℕ
  Fin→Nat {0} ()
  Fin→Nat {suc n} zero = zero
  Fin→Nat {suc n} (suc m) = suc (Fin→Nat m)

  minus : (n : ℕ) → Fin n → Fin (suc n)
  minus 0 ()
  minus (suc n) zero = n→Fin[n+1] (suc n)
  minus (suc n) (suc m) = Fin[n]→Fin[n+1] (minus n m)


  minusModN : (n : ℕ) → Fin n → Fin n
  minusModN 0 ()
  minusModN (suc n) zero = zero
  minusModN (suc n) (suc m) = minus n m


  div-helper : ℕ → (n : ℕ) → ℕ × (Fin (suc n)) → ℕ × ℕ
  div-helper 0       n (d , zero)          = ((suc d) , 0)
  div-helper 0       n (d , (suc r))       = (d , Fin→Nat (minusModN (suc n) (suc r)))
  div-helper (suc x) n (d , zero)          = div-helper x n ((suc d) , (n→Fin[n+1] n))
  div-helper (suc x) n (d , (suc r))       = div-helper x n (d , (Fin[n]→Fin[n+1] r))

  _÷_ : ℕ → (n : ℕ) → Maybe (ℕ × ℕ)
  (x ÷ 0)       = Nothing
  (0 ÷ (suc n)) = Just (0 , 0)
  ((suc x) ÷ (suc n)) = Just (div-helper x n (0 , (n→Fin[n+1] n)))
  
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
 module BinaryPredicates where
  open Operations
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
  open BaseDefinitions.Negation.Definition
  open BaseDefinitions.Void
  open BaseDefinitions.Unit
  open BaseDefinitions.Sum
  open BaseDefinitions.Product
  open BaseDefinitions.Equality.Definition
  open BaseResults
  open Equality.Properties
  open BaseDefinitions.Nat renaming (Nat to ℕ)
  open Operations hiding (_+_ ; _*_)
  open Functions.Special
  open Functions.Predicates
  open Functions.Composition.Definition
  open BinaryPredicates hiding (_≤_ ; _<_)
  open Relations.Properties.Totality
  open Relations.BinaryRelations.Properties.Antisymmetry
  open Relations.BinaryRelations.Properties.Irreflexivity
  open Relations.BinaryRelations.Properties.Asymmetry
  open LogicFunctionProperties

  ℕ-rec : ∀ {i} {P : ℕ → Set i} → P 0 → ({n : ℕ} → P n → P (suc n)) → ((n : ℕ) → P n)
  ℕ-rec {P = P} z s 0 = z
  ℕ-rec {P = P} z s (suc n) = s (ℕ-rec {P = P} z s n)

  _+_ : ℕ → ℕ → ℕ
  _+_ x = ℕ-rec x suc

  _*_ : ℕ → ℕ → ℕ
  _*_ x = ℕ-rec 0 (λ y → y + x)
  
  sx≠x : {x : ℕ} → (suc x) ≠ x
  sx≠x {x} ()

  x+sy=sx+y : (x y : ℕ) → (x + (suc y)) ≡ ((suc x) + y)
  x+sy=sx+y x = ℕ-rec refl (cong suc)

  sx+y=x+sy : (x y : ℕ) → ((suc x) + y) ≡ (x + (suc y))
  sx+y=x+sy x = ℕ-rec refl (cong suc)


  -- 1) ℕ is Dedekind infinite; suc is injective and proper
  -- almost formalizing the argument "The nats are infinite because we can always add 1 to get another Nat, and that Nat will be new"
  suc-inj : suc isInjective
  suc-inj p = cong pred p

  isZero : ℕ → Set
  isZero 0 = ⊤
  isZero (suc x) = ⊥

  sx≠0 : {x : ℕ} → (suc x) ≠ 0
  sx≠0 p = ⊤≠⊥ (≡-sym (cong isZero p))

  suc-proper : ¬ (suc isSurjective)
  suc-proper f = ω (⊤≠⊥ (≡-sym (cong isZero (π₂ (f 0)))))

  x+sy≠x : {x y : ℕ} → (x + (suc y)) ≠ x
  x+sy≠x {x}       {0}     p  = sx≠x p
  x+sy≠x {0}       {suc y} p  = sx≠0 p
  x+sy≠x {suc x}   {suc y} p  = x+sy≠x {x} {suc y} (cong pred (≡-trans (≡-sym (sx+y=x+sy x (suc (suc y)))) p))


  -- 2) 0 is the identity element for addition
  x=0+x : (x : ℕ) → x ≡ (0 + x)
  x=0+x = ℕ-rec refl (cong suc)

  0+-unique : (x y : ℕ) → (x + y) ≡ x → y ≡ 0
  0+-unique x 0 p = refl
  0+-unique x (suc y) p = ω (x+sy≠x {x} {y} p)
  
  0*x=0 : (x : ℕ) → (0 * x) ≡ 0
  0*x=0 = ℕ-rec refl id -- 0*x=0→0*sx=0 0*sx = 0*x+0=0*x=0

  0=0*x : (x : ℕ) → 0 ≡ (0 * x)
  0=0*x = ℕ-rec refl id

  0*-unique : (x y : ℕ) → (x * y) ≡ 0 → (x ≡ 0) ∨ (y ≡ 0)
  0*-unique 0       x       p = inl refl
  0*-unique (suc x) 0       p = inr refl
  0*-unique (suc x) (suc y) ()

  n=n-0 : (n : ℕ) → n ≡ (n - 0)
  n=n-0 0 = refl
  n=n-0 (suc n) = refl

  +-comm-ind : {x : ℕ} {y : ℕ} → (x + y) ≡ (y + x) → (x + (suc y)) ≡ ((suc y) + x)
  +-comm-ind {x} {y} p = ≡-trans (cong suc p) (x+sy=sx+y y x)

  -- 3) Addition is commutative
  -- a nicer proof of this would be nice
  +-comm : (x y : ℕ) → (x + y) ≡ (y + x)
  +-comm x = ℕ-rec (x=0+x x) (+-comm-ind {x})

  -- 4) Addition is associative
  +-assoc : (x y z : ℕ) → (x + (y + z)) ≡ ((x + y) + z)
  +-assoc x y = ℕ-rec refl (cong suc)

  -- so (ℕ,+) is a commutative monoid

  _≤_ : (x y : ℕ) → Set
  x ≤ y = ∃ k ∈ ℕ , ((x + k) ≡ y)

  _<_ : (x y : ℕ) → Set
  x < y = ∃ k ∈ ℕ , ((x + (suc k)) ≡ y)

  𝕤x≰0 : {x : ℕ} → ¬ ((suc x) ≤ 0)
  𝕤x≰0 {x} (k , 𝕤x+k=0) = sx≠0 (≡-trans (≡-sym (sx+y=x+sy x k)) 𝕤x+k=0)


  0≤x : (x : ℕ) → 0 ≤ x
  0≤x x = (x , ≡-sym (x=0+x x))
  
  0≤-unique : (y : ℕ) → ((x : ℕ) → y ≤ x) → y ≡ 0
  0≤-unique 0 f = refl
  0≤-unique (suc n) f = ω (𝕤x≰0 (f 0))

  -- successor is order-preserving
  x≤y→sx≤sy : {x y : ℕ} → x ≤ y → (suc x) ≤ (suc y)
  x≤y→sx≤sy {x} {y} (k , x+k=y) = k , ≡-trans (sx+y=x+sy x k) (cong suc x+k=y)

  sx≤sy→x≤y : {x y : ℕ} → (suc x) ≤ (suc y) → x ≤ y
  sx≤sy→x≤y {x} {y} (k , sx+k=sy) = k , cong pred (≡-trans (≡-sym (sx+y=x+sy x k)) sx+k=sy)

  x<y→sx<sy : {x y : ℕ} → x < y → (suc x) < (suc y)
  x<y→sx<sy {x} {y} (k , x+sk=y) = k , ≡-trans (sx+y=x+sy x (suc k)) (cong suc x+sk=y)

  sx<sy→x<y : {x y : ℕ} → (suc x) < (suc y) → x < y
  sx<sy→x<y {x} {y} (k , sx+sk=sy) = k , cong pred (≡-trans (≡-sym (sx+y=x+sy x (suc k))) sx+sk=sy)
  

  -- 5) ≤ is a total order
  -- reflexivity can also be defined relative to an equivalence relation
  ≤-refl : Reflexive _≤_
  ≤-refl x = (0 , refl)

  ≤-antisym : Antisymmetric _≡_ ≡-equiv _≤_
  ≤-antisym {zero} {zero} p q = refl
  ≤-antisym {zero} {suc y} p q = ω (𝕤x≰0 q)
  ≤-antisym {suc x} {zero} p q = ω (𝕤x≰0 p)
  ≤-antisym {suc x} {suc y} (k₁ , sx+k₁=sy) (k₂ , sy+k₂=sx) = cong suc (≤-antisym {x} {y} (k₁ , (cong pred (≡-trans (x+sy=sx+y x k₁) sx+k₁=sy))) (k₂ , (cong pred (≡-trans (x+sy=sx+y y k₂) sy+k₂=sx))))

  ≤-trans : Transitive _≤_
  ≤-trans {x} {y} {z} (k₁ , x+k₁=y) (k₂ , y+k₂=z) = (k₁ + k₂) , ≡-trans (+-assoc x k₁ k₂) (≡-trans (cong (λ q → q + k₂) x+k₁=y) y+k₂=z)

  ≤-total : Total _≤_
  ≤-total 0 y = inl (y , ≡-sym (x=0+x y))
  ≤-total (suc x) 0 = inr ((suc x) , ≡-sym (x=0+x (suc x)))
  ≤-total (suc x) (suc y) = ∨-map x≤y→sx≤sy x≤y→sx≤sy (≤-total x y) -- : x ≤ y ∨ y ≤ x


  ≤-leq₁ : {x y : ℕ} → (x ≤ y) → (x < y) ∨ (x ≡ y)
  ≤-leq₁ {x} {y} (0 , p) = inr p
  ≤-leq₁ {x} {y} (suc k , p) = inl (k , p)

  ≤-leq₂ : {x y : ℕ} → (x < y) ∨ (x ≡ y) → x ≤ y
  ≤-leq₂ {x} {y} (inl (k , p)) = (suc k , p)
  ≤-leq₂ {x} {.x} (inr refl) = ≤-refl x


  -- 6) _<_ is a strict total order
  
  <-irrefl : Irreflexive _<_
  <-irrefl {x} (k , x+sk=x) = ω (x+sy≠x {x} {k} x+sk=x)

  <-asymm : Asymmetric _<_
  <-asymm {x} {y} (k₁ , x+sk₁=y) (k₂ , y+sk₂=x) = <-irrefl (((suc k₁) + k₂) , (≡-trans (+-assoc x (suc k₁) (suc k₂)) (≡-trans (cong (λ q → q + (suc k₂)) x+sk₁=y) y+sk₂=x)))

  
  <-trichotomy : (x y : ℕ) → ((x < y) ∨ (x ≡ y) ∨ (y < x))
  <-trichotomy 0 0 = inr (inl refl)
  <-trichotomy 0 (suc y) = inl (y , ≡-sym (x=0+x (suc y)))
  <-trichotomy (suc x) 0 = inr (inr (x , ≡-sym (x=0+x (suc x))))
  <-trichotomy (suc x) (suc y) = ∨-map x<y→sx<sy (∨-map (cong suc) x<y→sx<sy) (<-trichotomy x y)

  
  <-trans : Transitive _<_
  <-trans {x} {y} {z} (k₁ , x+sk₁=y) (k₂ , y+sk₂=z) = ((suc k₁) + k₂) , ≡-trans (+-assoc x (suc k₁) (suc k₂)) (≡-trans (cong (λ q → q + (suc k₂)) x+sk₁=y) y+sk₂=z)


  x<y→x≠y : {x y : ℕ} → x < y → x ≠ y
  x<y→x≠y {x} {.x} (k , x+sk=x) refl = x+sy≠x {x} {k} x+sk=x 

  x<y→y≰x : {x y : ℕ} → x < y → ¬ (y ≤ x)
  x<y→y≰x p q = x<y→x≠y p (≤-antisym (≤-leq₂ (inl p)) q)

  𝕤x≰x : {x : ℕ} → ¬ ((suc x) ≤ x)
  𝕤x≰x {x} = x<y→y≰x {x} {suc x} (0 , refl)

  ℕ-unbounded : ¬ (∃ x ∈ ℕ , ((y : ℕ) → y ≤ x))
  ℕ-unbounded (x , f) = 𝕤x≰x (f (suc x))


  diff-x-x=0 : (x : ℕ) → (diff x x) ≡ 0
  diff-x-x=0 = ℕ-rec refl id

  {-
  diff as metric on ℕ
  -}
  -- inherently greater than 0
  -- diff x y = 0 → x = y
  diff-IoI : (x y : ℕ) → (diff x y) ≡ 0 → x ≡ y
  diff-IoI 0       0       p = refl
  diff-IoI 0       (suc y) ()
  diff-IoI (suc x) 0       ()
  diff-IoI (suc x) (suc y) p = cong suc (diff-IoI x y p)

  diff-IoI₂ : (x y : ℕ) → x ≡ y → (diff x y) ≡ 0
  diff-IoI₂ 0       0       p  = refl
  diff-IoI₂ 0       (suc x) ()
  diff-IoI₂ (suc x) 0       ()
  diff-IoI₂ (suc x) (suc y) p  = diff-IoI₂ x y (cong pred p)

  diff-comm : (x y : ℕ) → (diff x y) ≡ (diff y x)
  diff-comm 0       0       = refl
  diff-comm 0       (suc y) = refl
  diff-comm (suc x) 0       = refl
  diff-comm (suc x) (suc y) = diff-comm x y

  +-lemma1 : {x y z z' : ℕ} → (x + z) ≡ y → (x + z') ≡ y → z ≡ z'
  +-lemma1 {x} {y}     {0}     {0}      p q = refl
  +-lemma1 {x} {y}     {0}     {suc z'} p q = ω (x+sy≠x {x} {z'} (≡-trans q (≡-sym p)))
  +-lemma1 {x} {y}     {suc z} {0}      p q = ω (x+sy≠x {x} {z} (≡-trans p (≡-sym q)))
  +-lemma1 {x} {0}     {suc z} {suc z'} ()
  +-lemma1 {x} {suc y} {suc z} {suc z'} p q = cong suc (+-lemma1 {x} {y} (cong pred p) (cong pred q))
  
  ≤-lemma1 : {x y : ℕ} → x ≤ y → y ≡ (x + (diff x y))
  ≤-lemma1 {0}       {0}         p       = refl
  ≤-lemma1 {0}       {(suc y)}   p       = x=0+x (suc y)
  ≤-lemma1 {(suc x)} {0}         (k , p) = ω (sx≠0 (≡-trans (≡-sym (sx+y=x+sy x k)) p))
  ≤-lemma1 {(suc x)} {(suc y)}   (k , p) = ≡-trans (cong suc (≤-lemma1 {x} {y} (sx≤sy→x≤y (k , p)))) (≡-sym (sx+y=x+sy x (diff x y)))


  ∧-sym : ∀ {i j} {A : Set i} {B : Set j} → A ∧ B → B ∧ A
  ∧-sym (a , b) = b , a

  ∧-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → A ∧ B → B ∧ C → A ∧ C
  ∧-trans (a , b) (b' , c) = a , c

  ∨-sym : ∀ {i j} {A : Set i} {B : Set j} → A ∨ B → B ∨ A
  ∨-sym (inl a) = inr a
  ∨-sym (inr b) = inl b
  
  ≤-range-trichotomy : (x y z : ℕ) → x ≤ z → (y < x) ∨ (((x ≤ y) ∧ (y ≤ z)) ∨ (z < y))
  ≤-range-trichotomy x y z p = proof
   where
    lemma1 : (y < x) ∨ (y ≡ x) ∨ (x < y)
    lemma1 = <-trichotomy y x

    lemma2 : (z < y) ∨ (z ≡ y) ∨ (y < z)
    lemma2 = <-trichotomy z y

    lemma3 : (y < x) ∨ (y ≡ x) ∨ (x < y) → (z < y) ∨ (z ≡ y) ∨ (y < z) → (y < x) ∨ ((x ≤ y) ∧ (y ≤ z)) ∨ (z < y)
    lemma3 (inl y<x) q         = inl y<x
    lemma3 p         (inl z<y) = inr (inr z<y)
    lemma3 (inr p)   (inr q)   = inr (inl (≤-leq₂ (∨-map id ≡-sym (∨-sym p)) , ≤-leq₂ (∨-map id ≡-sym (∨-sym q))))

    proof = lemma3 lemma1 lemma2
  

  -- simplify this proof
  diff-triangle₁ : {x y z : ℕ} → (x ≤ y) → (y ≤ z) → (diff x z) ≡ ((diff x y) + (diff y z))
  diff-triangle₁ {x} {y} {z} p q = +-lemma1 (≡-sym (≤-lemma1 (≤-trans p q))) (≡-sym (≡-trans (≤-lemma1 q) (≡-trans (cong (λ r → r + (diff y z)) (≤-lemma1 p)) (≡-sym (+-assoc x (diff x y) (diff y z))))))
  {-
   ≤-lemma1 p : y=x+diffxy ;
   ≤-lemma1 q : z=y+diffyz ;

   ≡-trans (≤-lemma1 q) (cong (λ r → r + (diff y z)) (≤-lemma1 p)) : z=x+diffxy+diffyz;
   ≤-lemma1 (≤-trans p q) : z = x+diffxz
   +-lemma1 (≡-sym (≤-lemma1 (≤-trans p q))) (≡-trans (≤-lemma1 q) (cong (λ r → r + (diff y z)) (≤-lemma1 p)))               : diffxz=(diffxy+diffyz) 
  -}


  -- simplify this proof
  diff-triangle₂ : {x y z : ℕ} → (y < x) → (x ≤ z) → ((diff x z) + ((diff x y) * 2)) ≡ ((diff x y) + (diff y z))
  diff-triangle₂ {x} {y} {z} y<x x≤z = proof
   where
    y≤x : y ≤ x
    y≤x = ≤-leq₂ (inl y<x)

    y≤z : y ≤ z
    y≤z = ≤-trans y≤x x≤z

    lemma1 : x ≡ (y + (diff y x))
    lemma1 = ≤-lemma1 y≤x

    lemma2 : (y + (diff y x)) ≡ (y + (diff x y))
    lemma2 = cong (_+_ y) (diff-comm y x)

    lemma3 : x ≡ (y + (diff x y))
    lemma3 = ≡-trans lemma1 lemma2

    lemma4 : z ≡ (x + (diff x z))
    lemma4 = ≤-lemma1 x≤z

    lemma5 : z ≡ (y + ((diff x y) + (diff x z)))
    lemma5 = ≡-trans lemma4 (≡-trans (cong (λ q → q + (diff x z)) lemma3) (≡-sym (+-assoc y (diff x y) (diff x z))))

    lemma6 : z ≡ (y + (diff y z))
    lemma6 = ≤-lemma1 y≤z

    lemma7 : (diff y z) ≡ ((diff x y) + (diff x z))
    lemma7 = +-lemma1 {y} {z} {(diff y z)} {((diff x y) + (diff x z))} (≡-sym lemma6) (≡-sym lemma5)

    lemma8 : ((diff x y) * 2) ≡ ((0 + (diff x y)) + (diff x y))
    lemma8 = refl

    lemma9 : ((0 + (diff x y)) + (diff x y)) ≡ (0 + ((diff x y) + (diff x y)))
    lemma9 = ≡-sym (+-assoc 0 (diff x y) (diff x y))

    lemma10 : (0 + ((diff x y) + (diff x y))) ≡ ((diff x y) + (diff x y))
    lemma10 = ≡-sym (x=0+x ((diff x y) + (diff x y)))

    lemma11 : ((diff x y) * 2) ≡ ((diff x y) + (diff x y))
    lemma11 = ≡-trans lemma9 lemma10

    lemma12 : ((diff x z) + ((diff x y) * 2)) ≡ ((diff x z) + ((diff x y) + (diff x y)))
    lemma12 = cong (_+_ (diff x z)) lemma11

    lemma13 : ((diff x z) + ((diff x y) + (diff x y))) ≡ (((diff x z) + (diff x y)) + (diff x y))
    lemma13 = +-assoc (diff x z) (diff x y) (diff x y)

    lemma14 : ((diff x z) + (diff x y)) ≡ ((diff x y) + (diff x z))
    lemma14 = +-comm (diff x z) (diff x y)
    
    lemma15 : ((diff x z) + (diff x y)) ≡ (diff y z)
    lemma15 = ≡-trans lemma14 (≡-sym lemma7)

    lemma16 : (((diff x z) + (diff x y)) + (diff x y)) ≡ ((diff y z) + (diff x y))
    lemma16 = cong (λ q → q + (diff x y)) lemma15

    lemma17 : ((diff y z) + (diff x y)) ≡ ((diff x y) + (diff y z))
    lemma17 = +-comm (diff y z) (diff x y)

    proof = ≡-trans lemma12 (≡-trans lemma13 (≡-trans lemma16 lemma17))

  diff-triangle₂' : {x y z : ℕ} → (y < x) → (x ≤ z) → (diff x z)  ≤ ((diff x y) + (diff y z))
  diff-triangle₂' {x} {y} {z} y<x x≤z = ((diff x y) * 2) , diff-triangle₂ y<x x≤z
  {-
  ≤-lemma1 p : x=y+diffyx
  ≤-lemma1 q : z=x+diffxz
  ≤-lemma1 (≤-leq₁ (inl p)) : z = y + diffyz
   

  ≡-trans (≤-lemma1 q) (cong (λ r → r + (diff x z))) : z=y+diffyx + diffxz
  +-lemma1 ≤-lemma1 (≤-leq₁ (inl p)) (≡-trans (≤-lemma1 q) (cong (λ r → r + (diff x z)))) : diffyz = diffyx+diffxz
  diffxy + diffyz = diffxy + (diffyx + diffxz)
  diffxy + (diffyx+diffxz) = diffxz + 2*(diffxy)
  -}

  diff-triangle₃ : {x y z : ℕ} → (x ≤ z) → (z < y) →  ((diff x z) + ((diff y z) * 2)) ≡ ((diff x y) + (diff y z))
  diff-triangle₃ {x} {y} {z} x≤z z<y = proof
   where
    z≤y : z ≤ y
    z≤y = ≤-leq₂ (inl z<y)

    x≤y : x ≤ y
    x≤y = ≤-trans x≤z z≤y

    lemma1 : z ≡ (x + (diff x z))
    lemma1 = ≤-lemma1 x≤z

    lemma2 : y ≡ (z + (diff z y))
    lemma2 = ≤-lemma1 z≤y

    lemma3 : y ≡ (x + (diff x y))
    lemma3 = ≤-lemma1 x≤y

    lemma4 : y ≡ (x + ((diff x z) + (diff z y)))
    lemma4 = ≡-trans lemma2 (≡-trans (cong (λ q → q + (diff z y)) lemma1) (≡-sym (+-assoc x (diff x z) (diff z y))))

    lemma5 : (diff x y) ≡ ((diff x z) + (diff z y))
    lemma5 = +-lemma1 (≡-sym lemma3) (≡-sym lemma4)

    lemma6 : (diff x y) ≡ ((diff x z) + (diff y z))
    lemma6 = ≡-trans lemma5 (cong (_+_ (diff x z)) (diff-comm z y)) 

    lemma7 : ((diff x y) + (diff y z)) ≡ ((diff x z) + ((diff y z) + (diff y z)))
    lemma7 = ≡-trans (cong (λ q → q + (diff y z)) lemma6) (≡-sym (+-assoc (diff x z) (diff y z) (diff y z)))

    lemma8 : ((diff y z) + (diff y z)) ≡ (0 + ((diff y z) + (diff y z)))
    lemma8 = x=0+x ((diff y z) + (diff y z))

    lemma9 : (0 + ((diff y z) + (diff y z))) ≡ ((0 + (diff y z)) + (diff y z))
    lemma9 = +-assoc 0 (diff y z) (diff y z)

    lemma10 : ((diff y z) + (diff y z)) ≡ ((0 + (diff y z)) + (diff y z))
    lemma10 = ≡-trans lemma8 lemma9

    lemma11 : ((diff x z) + ((diff y z) + (diff y z))) ≡ ((diff x z) + ((diff y z) * 2))
    lemma11 = cong (_+_ (diff x z)) lemma10

    proof = ≡-sym (≡-trans lemma7 lemma11)

  diff-triangle₃' : {x y z : ℕ} → (x ≤ z) → (z < y) →  (diff x z) ≤ ((diff x y) + (diff y z))
  diff-triangle₃' {x} {y} {z} p q = (((diff y z) * 2) , diff-triangle₃ p q)

  ∨-ind : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (A → C) → (B → C) → A ∨ B → C
  ∨-ind f g (inl a) = f a
  ∨-ind f g (inr b) = g b


  diff-triangle : (x y z : ℕ) → (diff x z) ≤ ((diff x y) + (diff y z))
  diff-triangle x y z = ∨-ind f (g ∘ f) (≤-total x z)  -- x ≤ z ∨ z ≤ x
   where
    f : {a b : ℕ} → (a ≤ b) → (diff a b) ≤ ((diff a y) + (diff y b))
    f {a} {b} a≤b = ∨-ind g (∨-ind h i) (≤-range-trichotomy a y b a≤b)
     where
      g = λ p → diff-triangle₂' p a≤b
      h = λ p → ≤-leq₂ (inr (diff-triangle₁ (first p) (second p)))
      i = λ p → diff-triangle₃' a≤b p

    g : {a b : ℕ} → (diff a b) ≤ ((diff a y) + (diff y b)) → (diff b a) ≤ ((diff b y) + (diff y a))
    g {a} {b} (k , ab+k=ay+yb) = (k , ≡-trans (≡-sym (cong (λ q → q + k) (diff-comm a b))) (≡-trans ab+k=ay+yb (≡-trans (cong (λ q → q + (diff y b)) (diff-comm a y)) (≡-trans (cong (_+_ (diff y a)) (diff-comm y b)) (+-comm (diff y a) (diff b y))))))


  {-
  *-comm-ind : {x y : ℕ} → (x * y) ≡ (y * x) → (x * (suc y)) ≡ ((suc y) * x)
  *-comm-ind {x} {y} p = ≡-trans (cong suc p) : x * y + x ≡ (suc y) * x

  
  *-comm : (x y : ℕ) → (x * y) ≡ (y * x)
  *-comm x = ℕ-rec (0=0*x x) (cong suc)
  -}

  {-
  *-assoc : (x y z : ℕ) → (x * (y * z))  ≡ ((x * y) * z)
  *-assoc x y = ℕ-rec refl (cong suc)
  -}

  {-
  ÷-lemma : (x y : ℕ) → ∃ z , (y ≡ (suc z)) → ((y * (first (x ÷ y))) + (second (x ÷ y))) ≡ x
  ÷-lemma x zero (z , ())
  ÷-lemma zero (suc z) (.z , refl) = 
  -}



module Containers2 where
 module Vector where
  module Operations where
   open BaseDefinitions.Vector
   open BaseDefinitions.Nat
   open BaseDefinitions.Fin
   open BaseArithmetic.Results
   open BaseArithmetic.FinOperations
   open Equality.Properties
   
   remove : ∀ {i} {A : Set i} {n : Nat} → Vector A (suc n) → Fin (suc n) → Vector A n
   remove {i} {A} {zero} (a ∷ []) zero = []
   remove {i} {A} {zero} (a ∷ []) (suc ())
   remove {i} {A} {suc n} (a ∷ as) zero = as
   remove {i} {A} {suc n} (a ∷ as) (suc x) = a ∷ (remove as x)

   Vector++ : ∀ {i} {A : Set i} {m n : Nat} → Vector A m → Vector A n → Vector A (m + n)
   Vector++ {i} {A} {0}     {n} []        v2 = coerce v2 (cong (Vector A) (x=0+x n))
   Vector++ {i} {A} {suc m} {n} (a ∷ as) v2 = coerce (a ∷ (Vector++ as v2)) (cong (Vector A) (x+sy=sx+y m n))

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
 open Equality.Properties
 open BaseArithmetic
 open BaseArithmetic.Operations
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
 open Relations
 open Relations.Properties.Reflexivity
 open Relations.Properties.Symmetry
 open Relations.Properties.Antisymmetry
 open Relations.Properties.Transitivity
 open BaseDefinitions.Equality.Definition
 open Equality.Properties
 -- algebraic structures; to bundle or not to bundle
 -- how to describe relationship between these?
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
 open Relations
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
 open BaseArithmetic.BinaryPredicates
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
 open BaseDefinitions.Equality.Definition
 open BaseDefinitions.Product
 
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

 _isSoundWrt₁_ : ∀ {i j} {A : Set i} → (A → Bool) → (A → Set j) → Set (i ⊔ j)
 _isSoundWrt₁_ {A = A} s S = {x : A} → (s x) ≡ true → S x

 _isCompleteWrt₁_ : ∀ {i j} {A : Set i} → (A → Bool) → (A → Set j) → Set (i ⊔ j)
 _isCompleteWrt₁_ {A = A} s S = {x : A} → S x → (s x) ≡ true

 _decides₁_ : ∀ {i j} {A : Set i} → (A → Bool) → (A → Set j) → Set (i ⊔ j)
 s decides₁ S = (s isSoundWrt₁ S) ∧ (s isCompleteWrt₁ S)

 _isSoundWrt₂_ : ∀ {i j} {A : Set i} → (A → A → Bool) → (A → A → Set j) → Set (i ⊔ j)
 _isSoundWrt₂_ {A = A} r R = {x y : A} → (r x y) ≡ true → R x y

 _isCompleteWrt₂_ : ∀ {i j} {A : Set i} → (A → A → Bool) → (A → A → Set j) → Set (i ⊔ j)
 _isCompleteWrt₂_ {A = A} r R = {x y : A} → R x y → (r x y) ≡ true

 _decides₂_ : ∀ {i j} {A : Set i} → (A → A → Bool) → (A → A → Set j) → Set (i ⊔ j)
 r decides₂ R = (r isSoundWrt₂ R) ∧ (r isCompleteWrt₂ R)


module Numbers where
 open BaseDefinitions.Void
 open BaseDefinitions.BaseTypes.Unit
 open BaseDefinitions.BaseTypes.Bool
 open Boolean.Operations hiding (_eq_)
 open Boolean.Complex
 open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
 open BaseDefinitions.BaseTypes.Fin
 open BaseDefinitions.Product
 open BaseDefinitions.Sum
 open BaseDefinitions.Equality.Definition
 open Equality.Properties
 open BaseArithmetic.Operations renaming (_÷_ to _divide_)
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
 x ≟ y = dite-ind {lzero} {λ b → (Dec (x ≡ y))} (x eq y) true-case false-case
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
  open Functions.Inverses.FunctionInverses
  open Functions.Predicates
  open Functions.Bijections
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

  ℕ*→ℕ₂ : ℕ* → ℕ
  ℕ*→ℕ₂ one = 0
  ℕ*→ℕ₂ (suc n*) = suc (ℕ*→ℕ₂ n*)

  ℕ*→ℕ₃ : ℕ* → ℕ
  ℕ*→ℕ₃ n = pred (ℕ*→ℕ n)

  ℕ→ℕ* : ℕ → ℕ*
  ℕ→ℕ* 0 = one
  ℕ→ℕ* (suc n) = suc (ℕ→ℕ* n)


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
  ℕ→ℕ*-inv : ℕ→ℕ* isInverseOfₑ ℕ*→ℕ₂
  ℕ→ℕ*-inv = (L-inv , R-inv)
   where
    L-inv : ℕ→ℕ* isLInverseOfₑ ℕ*→ℕ₂
    L-inv one = refl
    L-inv (suc n) = cong suc (L-inv n)
      
    R-inv : ℕ→ℕ* isRInverseOfₑ ℕ*→ℕ₂
    R-inv zero = refl
    R-inv (suc n) = cong suc (R-inv n)



    
  ℕ→ℕ*-bij : ℕ→ℕ* isBijective
  ℕ→ℕ*-bij = first (Inv-bij ℕ→ℕ* (ℕ*→ℕ₂ , (invₑ-sym {f = ℕ→ℕ*} {g = ℕ*→ℕ₂} ℕ→ℕ*-inv)))


 module NonZeroNat₂ where
  open Functions.Composition.Definition
  data NonZeroComp {A : Set} (f : A → A) : (A → A) → Set where
   unit : NonZeroComp f f
   _·_ : {h g : A → A} → NonZeroComp f h → NonZeroComp f g → NonZeroComp f (h ∘ g)
   
 

 module Primes where
  open BaseDefinitions.Sum
  open BaseDefinitions.Nat
  open BaseDefinitions.Equality.Definition
  open BaseArithmetic.BinaryPredicates
  
  Prime : Nat → Set
  Prime n = (a : Nat) → a divides n → (a ≡ n) ∨ (a ≡ 1)
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
    ℚ : Set
    ℚ = ℤ × ℕ

   module Fractions₅ where
    ℚ : Set
    ℚ = ℤ × ℕ*

   module Fractions₆ where
    ℚ : Set
    ℚ = ∃ q ∈ (ℤ × ℕ) , (∃ r ∈ ℕ , (r ≡ (suc (second q)))) 

   module FractionEquivalences where
    open Fractions
    open Fractions₂ renaming (ℚ to ℚ₂)
    open Fractions₃ renaming (ℚ to ℚ₃)
    open Fractions₄ renaming (ℚ to ℚ₄)
    open Fractions₅ renaming (ℚ to ℚ₅)
    open Fractions₆ renaming (ℚ to ℚ₆)
    open Functions.Composition.Definition
    open Functions.Predicates
    open Functions.Inverses.FunctionInverses
    open Functions.Bijections


    ℚ→ℚ₂ : ℚ → ℚ₂
    ℚ→ℚ₂ (a / b) = a / (ℕ→ℕ* b)

   
    
   
   module Fractions₇ where
    data ℚ : Set where
     _÷_ : ℤ → (n : ℕ) → {p : ((n eq 0) ≡ false)} → ℚ

    _/_ : ℤ → (n : ℕ) → {p : ((n eq 0) ≡ false)} → ℚ
    (z / 0) {()}
    (z / (suc n)) {refl} = (z ÷ (suc n)) {refl}

    {-
    2/3 : ℚ
    2/3 = (possuc 1) / 3
    -}

   module Fractions₈ where
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

   
   module Fractions₉ where
    
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
    open Containers.List.Operations
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

  -- addition on reals can be defined in terms of the limit addition formula for Cauchy sequences etc..
    -- http://www.oxfordmathcenter.com/drupal7/node/94
  -- multiplication on reals can be defined in terms of the limit multiplication formula for Cauchy sequences etc.. 
    --
  -- http://tutorial.math.lamar.edu/Classes/CalcI/LimitsProperties.aspx
  
 -- translation of terminating / repeating real power expansions into Rationals
 -- Errett Bishop's definition of real numbers; MrChico's implementation in Agda:
  -- https://github.com/MrChico/agda-stdlib/blob/clean/src/Data/Real.agda
  


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

  

{-
pythagorean theorem & euclidean distance formulae
euclidean metric a result of pure number theory?
 

-}

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
   open Relations.BinaryRelations.Properties.Reflexivity
   open Relations.BinaryRelations.Properties.Symmetry
   open Relations.BinaryRelations.Properties.Transitivity
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
   open Containers.List.Operations
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
   open Containers.List.Operations
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
   open BaseDefinitions.BaseTypes.List renaming (_∷_ to _,_)
   open Containers.List.Operations renaming (_++_ to List++ ; [_] to mkList)
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
    open Equality.Properties
    open BaseDefinitions.Sum
    open BaseDefinitions.Product
    open BaseDefinitions.BaseTypes.Nat
    open BaseDefinitions.BaseTypes.Bool
    open Relations.Properties.Reflexivity
    open Relations.Properties.Transitivity
    open BaseDefinitions.BaseTypes.Fin.Definition
    open BaseArithmetic.FinOperations
    open BaseDefinitions.BaseTypes.List
    open Containers.List.Operations renaming (_++_ to List++ ; [_] to mkList)
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
   open BaseDefinitions.BaseTypes.List renaming (_∷_ to _,_)
   open Containers.List.Operations renaming (_++_ to List++ ; [_]  to mkList)
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

   -- Reduction of SKI combinators to graph-rewriting:
   -- http://hackage.haskell.org/package/graph-rewriting-ski
   
   -- Reduction of SKI combinators to string-rewriting
   --

   -- John Lamping -- An algorithm for optimal lambda calculus reduction
   -- http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.90.2386
   -- https://www.reddit.com/r/haskell/comments/2zqtfk/why_isnt_anyone_talking_about_optimal_lambda/

module Equivalence where
 open Relations

module Sets where
 module PropositionalSets where
  open BaseDefinitions.Void
  open BaseDefinitions.Negation.Definition
  open BaseDefinitions.Product
  open BaseDefinitions.Sum
  open BaseDefinitions.Equality.Definition
  open BaseDefinitions.BaseTypes.Unit
  open Relations
  Subset : ∀ {i j} (A : Set i) → Set ((lsuc j) ⊔ i)
  Subset {i} {j} A = A → Set j

 -- finite sets with HITs
 -- https://dl.acm.org/citation.cfm?id=3167085

  _⊆_ : ∀ {i j k} {A : Set i} (X : Subset {i} {j} A) → (Y  : Subset {i} {k} A) → Set (i ⊔ (j ⊔ k))
  _⊆_ {i} {j} {k} {A} X Y = (a : A) → X a → Y a

  _~_ : ∀ {i j k} {A : Set i} (X : Subset {i} {j} A) → (Y : Subset {i} {k} A) → Set (i ⊔ (j ⊔ k))
  X ~ Y = (X ⊆ Y) ∧ (Y ⊆ X)

  _∈_ : ∀ {i j} {A : Set i} → A → (X : Subset {i} {j} A) → Set j
  a ∈ X = X a

  Inhabited : ∀ {i j} {A : Set i} → (X : Subset {i} {j} A) → Set (i ⊔ j)
  Inhabited {A = A} X = ∃ a ∈ A , (X a)

  [_] : ∀ {i} {A : Set i} → A → Subset {i} {i} A
  [ x ] a = x ≡ a

  _-_ : ∀ {i j} {A : Set i} → Subset {i} {j} A → A → Subset {i} {(i ⊔ j)} A
  (X - a) x = (X x) ∧ (x ≠ a)

  _∪_ : ∀ {i j k} {A : Set i} → Subset {i} {j} A → Subset {i} {k} A → Subset {i} {(j ⊔ k)} A
  (A ∪ B) x = (A x) ∨ (B x)

  _∩_ : ∀ {i j k} {A : Set i} → Subset {i} {j} A → Subset {i} {k} A → Subset {i} {(j ⊔ k)} A
  (A ∩ B) x = (A x) ∧ (B x)

-- A \ B = A ∩ (B ᶜ)
  -- symmetric difference
  -- https://en.wikipedia.org/wiki/Symmetric_difference
  _⨁_ : ∀ {i j k} {A : Set i} → Subset {i} {j} A → Subset {i} {k} A → Subset {i} {(j ⊔ k)} A
  (A ⨁ B) x = ((A x) ∧ (¬ (B x))) ∨ ((¬ (A x)) ∧ (B x))
  

  X∩Y⊆X : ∀ {i j k} {A : Set i} → (X : Subset {i} {j} A) → (Y : Subset {i} {k} A) → (X ∩ Y) ⊆ X
  X∩Y⊆X X Y a p = first p

  X∩Y⊆Y : ∀ {i j k} {A : Set i} → (X : Subset {i} {j} A) → (Y : Subset {i} {k} A) → (X ∩ Y) ⊆ Y
  X∩Y⊆Y X Y a p = second p

  X⊆X∪Y : ∀ {i j k} {A : Set i} → (X : Subset {i} {j} A) → (Y : Subset {i} {k} A) → X ⊆ (X ∪ Y)
  X⊆X∪Y X Y a Xa = inl Xa

  Y⊆X∪Y : ∀ {i j k} {A : Set i} → (X : Subset {i} {j} A) → (Y : Subset {i} {k} A) → Y ⊆ (X ∪ Y)
  Y⊆X∪Y X Y a Ya = inr Ya 

  _ᶜ : ∀ {i j} {A : Set i} → Subset {i} {j} A → Subset {i} {j} A
  (A ᶜ) x = ¬ (A x)

  [X∪Y]⊆[Y∪X] : ∀ {i j k} {A : Set i} → (X : Subset {i} {j} A) → (Y : Subset {i} {k} A) → (X ∪ Y) ⊆ (Y ∪ X)
  [X∪Y]⊆[Y∪X] {i} {j} {k} {A} X Y a (inl Xa) = inr Xa
  [X∪Y]⊆[Y∪X] {i} {j} {k} {A} X Y a (inr Ya) = inl Ya

  [X∩Y]⊆[Y∩X] : ∀ {i j k} {A : Set i} → (X : Subset {i} {j} A) → (Y : Subset {i} {k} A) → (X ∩ Y) ⊆ (Y ∩ X)
  [X∩Y]⊆[Y∩X] {i} {j} {k} {A} X Y a (Xa , Ya) = (Ya , Xa)


  

  
  FullSubset : ∀ {i} (A : Set i) → Subset {i} {lzero} A
  FullSubset A x = ⊤
  
  EmptySubset : ∀ {i} (A : Set i) → Subset {i} {lzero} A
  EmptySubset A x = ⊥

  ⊆-refl : ∀ {i j} {A : Set i} → (X : Subset {i} {j} A) → X ⊆ X
  ⊆-refl {i} {j} {A} X a Xa = Xa

  ⊆-trans :
   ∀ {i j k l} {A : Set i}
   {X : Subset {i} {j} A}
   {Y : Subset {i} {k} A}
   {Z : Subset {i} {l} A} →
   X ⊆ Y → Y ⊆ Z → X ⊆ Z
  ⊆-trans X⊆Y Y⊆Z a Xa = Y⊆Z a (X⊆Y a Xa)

  {-
  yesyyriyto5i[69=0u=8[9uo7ly6ugjtrfeyhrrt5k858uy-7[7uy
  -}


  {-
  -- any preorder R defines in a standard way:
   -- a partial order: by declaring x ~ y iff  R x y ∧ R y x
   -- an equivalence: by taking the symmetric closure
  -- all equivalence relations are partial orders using themselves as the
    -- underlying equivalence relation for the antisymmetry property
    
  ⊆-antisym : ∀ {i j k} {A : Set i} → (X : Subset {i} {j} A) → (Y : Subset {i} {k} A) → X ⊆ Y → Y ⊆ X → 

  -}

  ⨁-lemma : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → (X ~ Y) → ¬ (Inhabited (X ⨁ Y))
  ⨁-lemma X Y (X-sub-Y , Y-sub-X) (x , (inl (Xx , ¬Yx))) = ¬Yx (X-sub-Y x Xx)
  ⨁-lemma X Y (X-sub-Y , Y-sub-X) (x , (inr (¬Xx , Yx))) = ¬Xx (Y-sub-X x Yx)

  Disjoint₂ : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Set (i ⊔ (j ⊔ k)) 
  Disjoint₂ {i} {j} {k} {A} X Y = (a : A) → ¬ ((X a) ∧ (Y a)) 
  -- could also define as (X ∩ Y) ~ ∅

  Disjoint₂-1 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Set (i ⊔ (j ⊔ k))
  Disjoint₂-1 {i} {j} {k} {A} X Y = ((a : A) → ¬ ((X a) ∧ (Y a))) ∨ (X ~ Y)

  Disjoint₂-2 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Set (i ⊔ (j ⊔ k))
  Disjoint₂-2 {i} {j} {k} {A} X Y = ¬ ((Inhabited (X ∩ Y)) ∧ (Inhabited (X ⨁ Y)))

  -- this is probably the one to use
  Disjoint₂-3 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Set (i ⊔ (j ⊔ k))
  Disjoint₂-3 {i} {j} {k} {A} X Y = Inhabited (X ∩ Y) → X ~ Y

  Disjoint₂-4 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Set (i ⊔ (j ⊔ k))
  Disjoint₂-4 {i} {j} {k} {A} X Y = Inhabited (X ⨁ Y) → Disjoint₂ X Y
  
  Disjoint₂-0,1 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Disjoint₂ X Y → Disjoint₂-1 X Y
  Disjoint₂-0,1 X Y XY-disjoint-0 = inl XY-disjoint-0

  Disjoint₂-1,2 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Disjoint₂-1 X Y → Disjoint₂-2 X Y
  Disjoint₂-1,2 {i} {j} {k} {A} X Y (inl XY-disjoint-0) ((a , (Xa , Ya)) , X⨁Y) = XY-disjoint-0 a (Xa , Ya)
  Disjoint₂-1,2 {i} {j} {k} {A} X Y (inr (X-sub-Y , Y-sub-X)) (X∩Y , (a , inl (Xa , ¬Ya))) = ¬Ya (X-sub-Y a Xa)
  Disjoint₂-1,2 {i} {j} {k} {A} X Y (inr (X-sub-Y , Y-sub-X)) (X∩Y , (a , inr (¬Xa , Ya))) = ¬Xa (Y-sub-X a Ya)

  Disjoint₂-1,3 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Disjoint₂-1 X Y → Disjoint₂-3 X Y
  Disjoint₂-1,3 {i} {j} {k} {A} X Y (inl XY-disjoint-0) (a , (Xa , Ya)) = ω (XY-disjoint-0 a (Xa , Ya))
  Disjoint₂-1,3 {i} {j} {k} {A} X Y (inr X~Y) X∩Y = X~Y

  Disjoint₂-1,4 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Disjoint₂-1 X Y → Disjoint₂-4 X Y
  Disjoint₂-1,4 {i} {j} {k} {A} X Y (inl XY-disjoint-0) X⨁Y = XY-disjoint-0
  Disjoint₂-1,4 {i} {j} {k} {A} X Y (inr (X-sub-Y , Y-sub-X)) (a , (inl (Xa , ¬Ya))) b (Xb , Yb) = ¬Ya (X-sub-Y a Xa)
  Disjoint₂-1,4 {i} {j} {k} {A} X Y (inr (X-sub-Y , Y-sub-X)) (a , (inr (¬Xa , Ya))) b (Xb , Yb) = ¬Xa (Y-sub-X a Ya)

  Disjoint₂-3,4 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Disjoint₂-3 X Y → Disjoint₂-4 X Y
  Disjoint₂-3,4 {i} {j} {k} {A} X Y XY-disjoint-3 (a , (inl (Xa , ¬Ya))) b (Xb , Yb) = ¬Ya ((first (XY-disjoint-3 (b , (Xb , Yb)))) a Xa)
  Disjoint₂-3,4 {i} {j} {k} {A} X Y XY-disjoint-3 (a , (inr (¬Xa , Ya))) b (Xb , Yb) = ¬Xa ((second (XY-disjoint-3 (b , (Xb , Yb)))) a Ya)

  
  Disjoint₂-3,2 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Disjoint₂-3 X Y → Disjoint₂-2 X Y
  Disjoint₂-3,2 {i} {j} {k} {A} X Y XY-disjoint-3 (X∩Y , X⨁Y) = ⨁-lemma X Y (XY-disjoint-3 X∩Y) X⨁Y

  Disjoint₂-2,4 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Disjoint₂-2 X Y → Disjoint₂-4 X Y
  Disjoint₂-2,4 {i} {j} {k} {A} X Y XY-disjoint-2 X⨁Y x (Xx , Yx) = XY-disjoint-2 ((x , (Xx , Yx)) , X⨁Y)

  Disjoint₂-4,2 : ∀ {i j k} {A : Set i} (X : A → Set j) (Y : A → Set k) → Disjoint₂-4 X Y → Disjoint₂-2 X Y
  Disjoint₂-4,2 {i} {j} {k} {A} X Y XY-disjoint-4 ((x , (Xx , Yx)) , X⨁Y) = XY-disjoint-4 X⨁Y x (Xx , Yx)

  

  -- not really as useful because we can't constrain not to have (extensional) duplicates
  Disjoint : ∀ {i j k} {A : Set i} (P : ((A → Set j) → Set k)) → Set (i ⊔ ((lsuc j) ⊔ k))
  Disjoint {i} {j} {k} {A} P = (p q : (A → Set j)) → P p → P q → Disjoint₂ p q

  
  Disjoint-1 : ∀ {i j k} {A : Set i} (P : ((A → Set j) → Set k)) → Set (i ⊔ ((lsuc j) ⊔ k))
  Disjoint-1 {i} {j} {k} {A} P = (p q : (A → Set j)) → P p → P q → (Disjoint₂-1 p q)


  Disjoint-2 : ∀ {i j k} {A : Set i} (P : ((A → Set j) → Set k)) → Set (i ⊔ ((lsuc j) ⊔ k))
  Disjoint-2 {i} {j} {k} {A} P = (p q : (A → Set j)) → P p → P q → (Disjoint₂-2 p q)

  Disjoint-3 : ∀ {i j k} {A : Set i} (P : ((A → Set j) → Set k)) → Set (i ⊔ ((lsuc j) ⊔ k))
  Disjoint-3 {i} {j} {k} {A} P = (p q : (A → Set j)) → P p → P q → (Disjoint₂-3 p q)


  
  Covering : ∀ {i j k} {A : Set i} (P : ((A → Set j) → Set k)) → Set (i ⊔ ((lsuc j) ⊔ k))
  Covering {i} {j} {k} {A} P = (a : A) → ∃ p ∈ (A → Set j) , ((P p) ∧ (p a))


  Partition : ∀ {i j k} {A : Set i} (P : ((A → Set j) → Set k)) → Set (i ⊔ ((lsuc j) ⊔ k))
  Partition {i} {j} {k} {A} P = (Disjoint P) ∧ (Covering P)

  Partition-1 : ∀ {i j k} {A : Set i} (P : ((A → Set j) → Set k)) → Set (i ⊔ ((lsuc j) ⊔ k))
  Partition-1 {i} {j} {k} {A} P = (Disjoint-1 P) ∧ (Covering P)


  Partition-2 : ∀ {i j k} {A : Set i} (P : ((A → Set j) → Set k)) → Set (i ⊔ ((lsuc j) ⊔ k))
  Partition-2 {i} {j} {k} {A} P = (Disjoint-2 P) ∧ (Covering P)

  Partition-3 : ∀ {i j k} {A : Set i} (P : ((A → Set j) → Set k)) → Set (i ⊔ ((lsuc j) ⊔ k))
  Partition-3 {i} {j} {k} {A} P = (Disjoint-3 P) ∧ (Covering P)


  _is_-closed : ∀ {i j k} {A : Set i} (S : A → Set j) → (R : A → A → Set k) → Set (i ⊔ (j ⊔ k))
  _is_-closed {i} {j} {k} {A} S R = (x y : A) → S x → R x y → S y

  _has_-semiclosure_ : ∀ {i j k l} {A : Set i} (S : A → Set j) → (R : A → A → Set k) → (T : A → Set l) → Set (i ⊔ (j ⊔ (k ⊔ l)))
  S has R -semiclosure T = (S ⊆ T) ∧ (T is R -closed)

  -- notice the level-breaking, because FOL can't define closure
  _has_-closure_ : ∀ {i j k l m} {A : Set i} (S : A → Set j) → (R : A → A → Set k) → (T : A → Set l) → Set (i ⊔ (j ⊔ (k ⊔ (l ⊔ (lsuc m)))))
  _has_-closure_ {m = m} {A = A} S R T = (S has R -semiclosure T) ∧ ((U : A → Set m) → S has R -semiclosure U → T ⊆ U)

  closures-unique : ∀ {i j k} {A : Set i} {S : A → Set j} {R : A → A → Set k} {T U : A → Set j} → S has R -closure T → S has R -closure U → T ~ U
  closures-unique
   {A = A} {T = T} {U = U}
   (T-semiclosure , T-minimal)
   (U-semiclosure , U-minimal)
   = (T⊆U , U⊆T)
   where
    T⊆U = T-minimal U U-semiclosure 
    U⊆T = U-minimal T T-semiclosure

  -- define equivalence classes as ~-closed subsets
  -- no because this could include multiple equivalence classes
  
  _is-[_,_]-equivalenceClass : ∀ {i j k m} {A : Set i} (S : A → Set j) → (R : A → A → Set k) → Equivalence R → Set (i ⊔ (j ⊔ (k ⊔ (lsuc m))))  
  _is-[_,_]-equivalenceClass {m = m} {A = A} S R eq = ∃ x ∈ A , (_has_-closure_ {m = m} ([ x ]) R S)

  -- given an object, give back its equivalence class:
  mkEquiv : ∀ {i j} {A : Set i} → A → (_~_ : A → A → Set j) → Equivalence _~_ → Subset {i} {j} A
  mkEquiv {i} {j} {A} x _~_ eq y = x ~ y

  mkEquivClosureLemma : ∀ {i j m} {A : Set i} → (x : A) → (R : A → A → Set j) → (eq : Equivalence R) → _has_-closure_ {m = m} ([ x ]) R (mkEquiv x R eq)
  mkEquivClosureLemma {i} {j} {m} {A} x R eq = (( x-sub-S , S-closed) , S-minimal)
   where
    open Relations.Equivalence eq
    
    S : A → Set j
    S = mkEquiv x R eq
    
    x-sub-S : [ x ] ⊆ S
    x-sub-S .x refl = reflexive x
    
    S-closed : S is R -closed
    S-closed a b Sa Rab = transitive Sa Rab
    
    S-minimal : (T : A → Set m) → [ x ] has R -semiclosure T → S ⊆ T
    S-minimal T (x-sub-T , T-closed) a Rxa = Ta
     where
      Tx = x-sub-T x refl

      Ta = T-closed x a Tx Rxa
    

  mkEquivClassLemma : ∀ {i j m} {A : Set i} → (x : A) → (R : A → A → Set j) → (eq : Equivalence R) → _is-[_,_]-equivalenceClass {m = m} (mkEquiv x R eq) R eq
  mkEquivClassLemma x R eq = ( x , mkEquivClosureLemma x R eq)

  mkEquivIndependence : ∀ {i j} {A : Set i} → (x y : A) → (R : A → A → Set j) → (eq : Equivalence R) → R x y → (mkEquiv x R eq) ~ (mkEquiv y R eq)
  mkEquivIndependence {i} {j} {A} x y R eq Rxy = (<x>-sub-<y> , <y>-sub-<x>)
   where
    open Relations.Equivalence eq
    
    <x> = mkEquiv x R eq
    <y> = mkEquiv y R eq
    
    <x>-sub-<y> : <x> ⊆ <y>
    <x>-sub-<y> a Rxa = transitive (symmetric Rxy) Rxa
      

    <y>-sub-<x> : <y> ⊆ <x>
    <y>-sub-<x> a Rya = transitive Rxy Rya

  mkEquivMembershipLemma : ∀ {i j} {A : Set i} → (R : A → A → Set j) → (eq : Equivalence R) → (x y z : A) → ((mkEquiv x R eq) y) → ((mkEquiv x R eq) z) → R y z
  mkEquivMembershipLemma {i} {j} {A} R eq x y z Rxy Rxz = Ryz
   where
    open Relations.Equivalence eq
    Ryz = transitive (symmetric Rxy) Rxz

  EquivClassMembershipLemma1 : ∀ {i j k m} {A : Set i} (R : A → A → Set j) → (eq : Equivalence R) → (S : A → Set k) → (q : _is-[_,_]-equivalenceClass {m = m} S R eq) → (mkEquiv (π₁ q) R eq) ⊆ S
  EquivClassMembershipLemma1 {i} {j} {k} {m} {A} R eq S (x , (([x]-sub-S , S-closed), S-minimal)) a Rxa = Sa
   where
    <x> = mkEquiv x R eq

    Sx : S x
    Sx = [x]-sub-S x refl
    
    Sa = S-closed x a Sx Rxa

  
  
  EquivClassCharacterizationLemma : ∀ {i j k} {A : Set i} → (R : A → A → Set j) → (eq : Equivalence R) → (S : A → Set k) → _is-[_,_]-equivalenceClass {m = j} S R eq → ∃ x ∈ A , (S ~ (mkEquiv x R eq))
  EquivClassCharacterizationLemma {i} {j} {k} {A} R eq S (x , (S-semiclosure , S-minimal)) = x , (S-sub-<x> , <x>-sub-S)
   where
    <x> = mkEquiv x R eq

    [x]-closure : _has_-closure_ {m = k} [ x ] R <x> 
    [x]-closure = mkEquivClosureLemma {m = k} x R eq

    
    S-sub-<x> = S-minimal <x> (first [x]-closure)
    
    <x>-sub-S = (second [x]-closure) S S-semiclosure


  
  EquivClassMembershipLemma : ∀ {i j k} {A : Set i} (R : A → A → Set j) → (eq : Equivalence R) → (S : A → Set k) → _is-[_,_]-equivalenceClass {m = j} S R eq → (x y : A) → S x → S y → R x y
  EquivClassMembershipLemma {i} {j} {k} {A} R eq S (z , (([z]-sub-S , S-closed) , S-minimal)) x y Sx Sy = Rxy
   where
    open Relations.Equivalence eq
    
    <z> = mkEquiv z R eq
  
    characterization : ∃ q ∈ A , (S ~ (mkEquiv q R eq))
    characterization = EquivClassCharacterizationLemma R eq S (z , (([z]-sub-S , S-closed) , S-minimal))

    S-sub-<z> : S ⊆ <z>
    S-sub-<z> = first (π₂ characterization)

    Rzx : R z x
    Rzx = S-sub-<z> x Sx

    Rzy : R z y
    Rzy = S-sub-<z> y Sy

    Rxy : R x y
    Rxy = transitive (symmetric Rzx) Rzy


  -- given an equivalence relation, give back its equivalence classes
  getEquivs : ∀ {i j k m} {A : Set i} → (R : A → A → Set j) → Equivalence R → (A → Set k) → Set (i ⊔ (j ⊔ (k ⊔ (lsuc m))))
  getEquivs {i} {j} {k} {m} R eq S = _is-[_,_]-equivalenceClass {m = m} S R eq



  mkEquivDisjointnessLemma : ∀ {i j} {A : Set i} → (R : A → A → Set j) → (eq : Equivalence R) → (x y : A) → ¬ (R x y) → Disjoint₂ (mkEquiv x R eq) (mkEquiv y R eq)
  mkEquivDisjointnessLemma {i} {j} {A} R eq x y ¬Rxy a (Rxa , Rya) = ¬Rxy Rxy
   where
    open Relations.Equivalence eq
    Rxy = transitive Rxa (symmetric Rya)


  EquivClassIntersectionLemma : ∀ {i j k l} {A : Set i} → (R : A → A → Set j) → (eq : Equivalence R) → (S : A → Set k) → (T : A → Set l) → _is-[_,_]-equivalenceClass {m = j} S R eq → _is-[_,_]-equivalenceClass {m = j} T R eq → Inhabited (S ∩ T) → S ~ T
  EquivClassIntersectionLemma {i} {j} {k} {l} {A} R eq S T S-class T-class (a , (Sa , Ta)) = (S-sub-T , T-sub-S)
   where
    open Relations.Equivalence eq

    -- remove redundancies
    S-characterization : ∃ x ∈ A , (S ~ (mkEquiv x R eq))
    S-characterization = EquivClassCharacterizationLemma R eq S S-class

    x : A
    x = π₁ S-characterization

    <x> : A → Set j
    <x> = mkEquiv x R eq

    S-sub-<x> : S ⊆ <x>
    S-sub-<x> = first (π₂ S-characterization)

    <x>-sub-S : <x> ⊆ S
    <x>-sub-S = second (π₂ S-characterization)


    Rxa : R x a
    Rxa = S-sub-<x> a Sa

    T-characterization : ∃ y ∈ A , (T ~ (mkEquiv y R eq))
    T-characterization = EquivClassCharacterizationLemma R eq T T-class

    y : A
    y = π₁ T-characterization

    <y> : A → Set j
    <y> = mkEquiv y R eq

    T-sub-<y> : T ⊆ <y>
    T-sub-<y> = first (π₂ T-characterization)

    <y>-sub-T : <y> ⊆ T
    <y>-sub-T = second (π₂ T-characterization)

    Rya : R y a
    Rya = T-sub-<y> a Ta

    Rxy : R x y
    Rxy = transitive Rxa (symmetric Rya)

    <x>~<y> : <x> ~ <y>
    <x>~<y> = mkEquivIndependence x y R eq Rxy

    S-sub-T = ⊆-trans S-sub-<x> (⊆-trans (first <x>~<y>) <y>-sub-T) 
    T-sub-S = ⊆-trans T-sub-<y> (⊆-trans (second <x>~<y>) <x>-sub-S)

  EquivClassDifferenceLemma : ∀ {i j k l} {A : Set i} → (R : A → A → Set j) → (eq : Equivalence R) → (S : A → Set k) → (T : A → Set l) → _is-[_,_]-equivalenceClass {m = j} S R eq → _is-[_,_]-equivalenceClass {m = j} T R eq → Inhabited (S ⨁ T) → Disjoint₂ S T
  EquivClassDifferenceLemma {i} {j} {k} {l} {A} R eq S T S-class T-class (a , (inl (Sa , ¬Ta))) x (Sx , Tx) = contradiction
   where
    S~T : S ~ T
    S~T = EquivClassIntersectionLemma R eq S T S-class T-class (x , (Sx , Tx))   
    contradiction = ¬Ta ((first S~T) a Sa)
  EquivClassDifferenceLemma {i} {j} {k} {l} {A} R eq S T S-class T-class (a , (inr (¬Sa , Ta))) x (Sx , Tx) = contradiction
   where
    S~T : S ~ T
    S~T = EquivClassIntersectionLemma R eq S T S-class T-class (x , (Sx , Tx))      
    contradiction = ¬Sa ((second S~T) a Ta)
  

  
  EquivPartitionLemma : ∀ {i j} {A : Set i} → (R : A → A → Set j) → (eq : Equivalence R) → Partition-2 {i} {j} {i ⊔ (lsuc j)} {A} (getEquivs {i} {j} {j} {j} R eq)
  EquivPartitionLemma {i} {j} {A} R eq = (disjoint , covering)
   where
    open Relations.Equivalence eq
    
    P : (A → Set j) → Set (i ⊔ (lsuc j))
    P = getEquivs {i} {j} {j} {j} R eq

    covering : (a : A) → ∃ p ∈ (A → Set j) , ((P p) ∧ (p a))
    covering a = (mkEquiv a R eq , (P[a] , [a]a))
     where
      P[a] : P (mkEquiv a R eq)
      P[a] = mkEquivClassLemma a R eq
      
      [a]a : (mkEquiv a R eq) a
      [a]a = reflexive a
    
    
    disjoint : (p q : A → Set j) → P p → P q → Disjoint₂-2 p q
    disjoint p q Pp Pq ((a , (pa , qa)) , diff-pq) = EquivClassDifferenceLemma R eq p q Pp Pq diff-pq a (pa , qa) 

  EquivPartition3Lemma : ∀ {i j} {A : Set i} → (R : A → A → Set j) → (eq : Equivalence R) → Partition-3 {i} {j} {i ⊔ (lsuc j)} {A} (getEquivs {i} {j} {j} {j} R eq)
  EquivPartition3Lemma {i} {j} {A} R eq = (disjoint , covering)
   where
    open Relations.Equivalence eq
    
    P : (A → Set j) → Set (i ⊔ (lsuc j))
    P = getEquivs {i} {j} {j} {j} R eq

    covering : (a : A) → ∃ p ∈ (A → Set j) , ((P p) ∧ (p a))
    covering a = (mkEquiv a R eq , (P[a] , [a]a))
     where
      P[a] : P (mkEquiv a R eq)
      P[a] = mkEquivClassLemma a R eq
      
      [a]a : (mkEquiv a R eq) a
      [a]a = reflexive a
    
    disjoint : (p q : A → Set j) → P p → P q → Inhabited (p ∩ q) → p ~ q
    disjoint p q Pp Pq p∩q = EquivClassIntersectionLemma R eq p q Pp Pq p∩q

  PartitionClass : ∀ {i j k} {A : Set i} → (P : (A → Set j) → Set k) → Partition-2 P → A → A → Set (i ⊔ ((lsuc j) ⊔ k))
  PartitionClass {i} {j} {k} {A} P P-partition x y = ∃ p ∈ (A → Set j) , ((P p) ∧ (p x) ∧ (p y))

  Partition3Class : ∀ {i j k} {A : Set i} → (P : (A → Set j) → Set k) → Partition-3 P → A → A → Set (i ⊔ ((lsuc j) ⊔ k))
  Partition3Class {i} {j} {k} {A} P P-partition x y = ∃ p ∈ (A → Set j) , ((P p) ∧ (p x) ∧ (p y))

  PartitionClass-refl : ∀ {i j k} {A : Set i} → (P : (A → Set j) → Set k) → (P-partition : Partition-2 P) → (x : A) → PartitionClass P P-partition x x
  PartitionClass-refl {i} {j} {k} {A} P (P-disjoint , P-covering) x = (p , (Pp , (px , px)))
   where
    p = π₁ (P-covering x)
    Pp = first (π₂ (P-covering x))
    px = second (π₂ (P-covering x))

  Partition3Class-refl :  ∀ {i j k} {A : Set i} → (P : (A → Set j) → Set k) → (P-partition : Partition-3 P) → (x : A) → Partition3Class P P-partition x x
  Partition3Class-refl {i} {j} {k} {A} P (P-disjoint , P-covering) x = (p , (Pp , (px , px)))
   where
    p = π₁ (P-covering x)
    Pp = first (π₂ (P-covering x))
    px = second (π₂ (P-covering x))
    

  PartitionClass-symm : ∀ {i j k} {A : Set i} → (P : (A → Set j) → Set k) → (P-partition : Partition-2 P) → (x y : A) → PartitionClass P P-partition x y → PartitionClass P P-partition y x
  PartitionClass-symm {i} {j} {k} {A} P P-partition x y (p , (Pp , (px , py))) = (p , (Pp , (py , px)))

  Partition3Class-symm : ∀ {i j k} {A : Set i} → (P : (A → Set j) → Set k) → (P-partition : Partition-3 P) → {x y : A} → Partition3Class P P-partition x y → Partition3Class P P-partition y x
  Partition3Class-symm {i} {j} {k} {A} P P-partition {x} {y} (p , (Pp , (px , py))) = (p , (Pp , (py , px)))


  {-
  PartitionClass-trans : ∀ {i j k} {A : Set i} → (P : (A → Set j) → Set k) → (P-partition : Partition'' P) → (x y z : A) → PartitionClass P P-partition x y → PartitionClass P P-partition y z → PartitionClass P P-partition x z
  PartitionClass-trans {i} {j} {k} {A} P (P-disjoint , P-covering) x y z (p , (Pp , (px , py))) (q , (Pq , (qy , qz))) = (p , (Pp , (px , pz)))
   where
    pq-disjoint₂'' : ¬ ((Inhabited (p ∩ q)) ∧ (Inhabited (p ⨁ q)))
    pq-disjoint₂'' = P-disjoint p q Pp Pq

    p~q : ¬ (Inhabited (p ⨁ q))
    p~q p⨁q = P-disjoint₂'' ((y , (py , qy)) , 

    pz
  -}

  Partition3Class-trans : ∀ {i j k} {A : Set i} → (P : (A → Set j) → Set k) → (P-partition : Partition-3 P) → {x y z : A} → Partition3Class P P-partition x y → Partition3Class P P-partition y z → Partition3Class P P-partition x z
  Partition3Class-trans {i} {j} {k} {A} P (P-disjoint , P-covering) {x} {y} {z} (p , (Pp , (px , py))) (q , (Pq , (qy , qz))) = (p , (Pp , (px , pz)))
   where
    p~q : p ~ q
    p~q = P-disjoint p q Pp Pq (y , (py , qy))
    
    pz = (second p~q) z qz 

  Partition3Class-equiv : ∀ {i j k} {A : Set i} → (P : (A → Set j) → Set k) → (P-partition : Partition-3 P) → Equivalence (Partition3Class P P-partition)
  Partition3Class-equiv {i} {j} {k} {A} P P-partition =
   record{
    reflexive = Partition3Class-refl P P-partition ;
    symmetric = Partition3Class-symm P P-partition ;
    transitive = Partition3Class-trans P P-partition
   }

  -- now prove that this translation between partitions and equivalence classes
  -- is... an equivalence
  
  -- getEquivs : ∀ {i j k m} {A : Set i} → (R : A → A → Set j) → Equivalence R → (A → Set k) → Set (i ⊔ (j ⊔ (k ⊔ (lsuc m))))
  -- Partition3Class : ∀ {i j k} {A : Set i} → (P : (A → Set j) → Set k) → Partition-3 P → A → A → Set (i ⊔ ((lsuc j) ⊔ k))
  -- PartitionClass {i} {j} {k} {A} P P-partition x y = ∃ p ∈ (A → Set j) , ((P p) ∧ (p x) ∧ (p y))
 -- _is-[_,_]-equivalenceClass {m = m} {A = A} S R eq = ∃ x ∈ A , (_has_-closure_ {m = m} ([ x ]) R S)
  --  Covering {i} {j} {k} {A} P = (a : A) → ∃ p ∈ (A → Set j) , ((P p) ∧ (p a))
  -- EquivClassMembershipLemma : ∀ {i j k} {A : Set i} (R : A → A → Set j) → (eq : Equivalence R) → (S : A → Set k) → _is-[_,_]-equivalenceClass {m = j} S R eq → (x y : A) → S x → S y → R x y
   
  PartitionEquivLemma :
   ∀ {i j k} {A : Set i} →
   (P : (A → Set j) → Set k) →
   (P-partition : Partition-3 P) →
   (p : A → Set j) →
   _is-[_,_]-equivalenceClass
     {m = i ⊔ ((lsuc j) ⊔ k)}
     p
     (Partition3Class P P-partition)
     (Partition3Class-equiv P P-partition) →
   ∃ q ∈ (A → Set j) , ((P q) ∧ (p ~ q))
  PartitionEquivLemma
   {i} {j} {k} {A}
   P
   (P-disjoint , P-covering)
   p
   (x , (([x]-sub-p , p-closed) , p-minimal))
   = (q , (Pq , (p-sub-q , q-sub-p)))
    where
     R : A → A → Set (i ⊔ ((lsuc j) ⊔ k))
     R = Partition3Class P (P-disjoint , P-covering)

     eq : Equivalence R
     eq = Partition3Class-equiv P (P-disjoint , P-covering)

     px : p x
     px = [x]-sub-p x refl

     q = π₁ (P-covering x)
     Pq = first (π₂ (P-covering x))
     qx = second (π₂ (P-covering x))

     pa→Rxa : (a : A) → p a → R x a
     pa→Rxa a pa = EquivClassMembershipLemma R eq p (x , (([x]-sub-p , p-closed) , p-minimal)) x a px pa

     Rxa→qa : (a : A) → R x a → q a
     Rxa→qa a (r , (Pr , (rx , ra))) = qa
      where
       q~r : q ~ r
       q~r = P-disjoint q r Pq Pr (x , (qx , rx))
       
       qa = (second q~r) a ra

     qa→Rxa : (a : A) → q a → R x a
     qa→Rxa a qa = (q , (Pq , (qx , qa)))

     Rxa→pa : (a : A) → R x a → p a
     Rxa→pa a Rxa = p-closed x a px Rxa

     p-sub-q : (a : A) → p a → q a
     p-sub-q a pa = Rxa→qa a (pa→Rxa a pa)
       
     q-sub-p : (a : A) → q a → p a
     q-sub-p a qa = Rxa→pa a (qa→Rxa a qa)

  -- note that it doesn't suffice to just give the subset you have to
  -- give an inhabitant also
  PartitionEquivLemma2 :
   ∀ {i j k} {A : Set i} →
   (P : (A → Set j) → Set k) →
   (P-partition : Partition-3 P) →
   (p : A → Set j) → P p → (a : A) → p a → 
   ∃ q ∈ (A → Set j) ,
    ((_is-[_,_]-equivalenceClass
     {m = i ⊔ ((lsuc j) ⊔ k)}
     q
     (Partition3Class P P-partition)
     (Partition3Class-equiv P P-partition)
    ) ∧ (p ~ q))
  PartitionEquivLemma2 {i} {j} {k} {A} P P-partition p Pp a pa = (p , (((a , (([a]-sub-p , p-closed) , p-minimal))) , (p-sub-p , p-sub-p)))
   where
    R : A → A → Set (i ⊔ ((lsuc j) ⊔ k))
    R = Partition3Class P P-partition

    eq : Equivalence R
    eq = Partition3Class-equiv P P-partition

    P-disjoint = first P-partition
    P-covering = second P-partition

    -- ∃ p ∈ (A → Set j) , ((P p) ∧ (p x) ∧ (p y))
 
    [a]-sub-p : (x : A) → [ a ] x → p x
    [a]-sub-p .a refl = pa
    
    p-closed : (x y : A) → p x → R x y → p y
    p-closed x y px (r , (Pr , (rx , ry))) = (second (P-disjoint p r Pp Pr (x , (px , rx)))) y ry


    px→Rax : (x : A) → p x → R a x
    px→Rax x px = (p , (Pp , (pa , px)))

    p-minimal : (U : A → Set (i ⊔ ((lsuc j) ⊔ k))) → [ a ] has R -semiclosure U → p ⊆ U
    p-minimal U ([a]-sub-U , U-closed) x px = Ux
     where
      Ua : U a
      Ua = [a]-sub-U a refl
      
      Rax→Ux : R a x → U x
      Rax→Ux Rax = U-closed a x Ua Rax
      
      Ux = Rax→Ux (px→Rax x px) 
      
    p-sub-p = ⊆-refl p

  Equiv-comp : ∀ {i j} {A : Set i} (R : A → A → Set j) → Equivalence R → {x y z : A} → R x y → R y z → R x z
  Equiv-comp {i} {j} {A} R eq {x} {y} {z} Rxy Ryz = transitive Rxy Ryz
   where
    open Relations.Equivalence eq

  Equiv-id-weak : ∀ {i j} {A : Set i} (R : A → A → Set j) → (eq : Equivalence R) → (x : A) → R x x
  Equiv-id-weak {i} {j} {A} R eq x = reflexive x
   where
    open Relations.Equivalence eq

  Equiv-inv-weak : ∀ {i j} {A : Set i} (R : A → A → Set j) → Equivalence R → {x y : A} → R x y → R y x
  Equiv-inv-weak {i} {j} {A} R eq {x} {y} Rxy = symmetric Rxy
   where
    open Relations.Equivalence eq

    
  -- with proof-irrelevance we can trivially get the actual laws
  -- without proof-irrelevance maybe not
  {-
  Equiv-id : ∀ {i j} {A : Set i} (R : A → A → Set j) → (eq : Equivalence R) → (x : A) → ∃ e ∈ (R x x) , (((y : A) → (Rxy : R x y) → (Equiv-comp R eq e Rxy) ≡ Rxy) ∧ ((y : A) → (Ryx : R y x) → (Equiv-comp R eq Ryx e) ≡ Ryx))
  Equiv-id {i} {j} {A} R eq x = (e , (e-idL , e-idR))
   where
    open BaseDefinitions.Relations.Equivalence eq
    
    e = reflexive x
    e-idL : (y : A) → (Rxy : R x y) → (Equiv-comp R eq e Rxy) ≡ Rxy
    e-idL y Rxy = refl
    
    e-idR : (y : A) → (Ryx : R y x) → (Equiv-comp R eq Ryx e) ≡ Ryx
    e-idR y Ryx = refl
  -}

  -- continuous functions
  -- https://www.cs.bham.ac.uk/~mhe/talks/escardo-ihp2014.pdf
  -- basically just the same as "Groupoid"
  record EquivGroupoid {i j} {A : Set i} (R : A → A → Set j) : Set (i ⊔ j) where
   field
    reflexivity : (x : A) → R x x
    symmetry : {x y : A} → R x y → R y x
    transitivity : {x y z : A} → R x y → R y z → R x z
    identities : {x y : A} → (Rxy : R x y) → ((transitivity (reflexivity x) Rxy) ≡ Rxy) ∧ ((transitivity Rxy (reflexivity y)) ≡ Rxy)
    inverses : {x y : A} → (Rxy : R x y) → ((transitivity Rxy (symmetry Rxy)) ≡ (reflexivity x)) ∧ ((transitivity (symmetry Rxy) Rxy) ≡ (reflexivity y))
    associativity : {w x y z : A} → (Rwx : R w x) → (Rxy : R x y) → (Ryz : R y z) → ((transitivity Rwx (transitivity Rxy Ryz)) ≡ (transitivity (transitivity Rwx Rxy) Ryz))
      
  ≡-EquivGroupoid : ∀ {i} {A : Set i} → EquivGroupoid {i} {i} {A} _≡_
  ≡-EquivGroupoid {i} {A} =
   record{
    reflexivity   = λ x → refl    ;
    symmetry      = ≡-sym         ;
    transitivity  = ≡-trans       ;
    identities    = ≡-id          ;
    inverses      = ≡-inv         ;
    associativity = ≡-assoc
   }
    where
     open Equality.Properties

     reflexivity : (a : A) → a ≡ a
     reflexivity a = refl

     ≡-id : {x y : A} → (x=y : x ≡ y) → ((≡-trans (reflexivity x) x=y) ≡ x=y) ∧ ((≡-trans x=y (reflexivity y)) ≡ x=y)
     ≡-id {x} {.x} refl = (refl , refl)

     ≡-inv : {x y : A} → (x=y : x ≡ y) → ((≡-trans x=y (≡-sym x=y)) ≡ (reflexivity x)) ∧ ((≡-trans (≡-sym x=y) x=y) ≡ (reflexivity y))
     ≡-inv {x} {.x} refl = (refl , refl)
     
     ≡-assoc : {w x y z : A} → (w=x : w ≡ x) → (x=y : x ≡ y) → (y=z : y ≡ z) → ((≡-trans w=x (≡-trans x=y y=z)) ≡ (≡-trans (≡-trans w=x x=y) y=z))
     ≡-assoc {w} {.w} {.w} {.w} refl refl refl = refl

  refl-unique : ∀ {i} {A : Set i} {x : A} → (p : x ≡ x) → p ≡ refl
  refl-unique {i} {A} {x} refl = refl

  refl-unique₂ : ∀ {i} {A : Set i} {x y : A} → (p q : x ≡ y) → p ≡ q
  refl-unique₂ {i} {A} {x} {.x} refl refl = refl

  

  {-
  BijectionGroupoid : ∀ {i} → EquivGroupoid {(lsuc i)} {i} {Set i} Functions.Predicates._hasBijectionWith_
  BijectionGroupoid {i} =
   record{
    reflexivity   = Bij-refl       ;
    symmetry      = Bij-symm       ;
    transitivity  = Bij-trans      ;
    identities    = id-bij         ;
    inverses      = Bij-inv        ;
    associativity = Bij-assoc
   }
    where
     open Functions.Composition.Definition
     open Functions.Predicates
     open Functions.Bijections

     identities = id-bij
     Bij-assoc : {w x y z : Set i} → (Rwx : w hasBijectionWith x) → (Rxy : x hasBijectionWith y) → (Ryz : y hasBijectionWith z) → ((Bij-trans Rwx (Bij-trans Rxy Ryz)) ≡ (Bij-trans (Bij-trans Rwx Rxy) Ryz))
     Bij-assoc
      {w} {x} {y} {z}
      (wx , (wx-inj , wx-surj))
      (xy , (xy-inj , xy-surj))
      (yz , (yz-inj , yz-surj))
      = proof
       where
        proof
   -}   
 module BooleanSets where
  open BaseDefinitions.Product
  open BaseDefinitions.Equality.Definition
  open BaseDefinitions.BaseTypes.Bool
  open Boolean.Operations
  open Functions.Composition.Definition
  open Functions.Special
  open Boolean.Operations
  open PropositionalSets using (Subset)
  subset : ∀ {i} (A : Set i) → Set i
  subset {i} A = A → Bool

  _⊆_ : ∀ {i} {A : Set i} (X Y : subset A) → Set i
  _⊆_ {i} {A} X Y = (a : A) → (X a ≡ true) → (Y a ≡ true)

  subset→Subset : ∀ {i} {A : Set i} → subset A → Subset A
  subset→Subset {i} {A} X a = X a ≡ true
     -- Dedekind infiniteness: the existence of a bijection between it and some proper subset of itself

  _∈_ : ∀ {i} {A : Set i} → A → (X : subset A) → Bool
  a ∈ X = X a

  _∪_ : ∀ {i} {A : Set i} → (X Y : subset A) → subset A
  (X ∪ Y) x = (X x) or (Y x)

  _∩_ : ∀ {i} {A : Set i} → (X Y : subset A) → subset A
  (X ∩ Y) x = (X x) and (Y x)

  {-
  X∩Y⊆X : ∀ {i} {A : Set i} → (X Y : Subset A) → (X ∩ Y)
  -}

  {-
  -- can only do this for sets with decidable equality!
  _-_ : ∀ {i} {A : Set i} → (X : subset A) → A → subset A
  (X - a) x = (X x) and (not (x == a))
  -}

  _ᶜ : ∀ {i} {A : Set i} → subset A → subset A
  (A ᶜ) x = not (A x) 

  fullsubset : ∀ {i} (A : Set i) → subset A
  fullsubset A x = true

  emptysubset : ∀ {i} (A : Set i) → subset A
  emptysubset A x = false

  lemma1 : Bool × Bool → (Bool → Bool)
  lemma1 = λ {(a , b) → (λ b → if b then (first (a , b)) else (second (a , b)))}

  lemma2 : (Bool → Bool) → Bool × Bool
  lemma2 f = (f true , f false)

  {-
  lemma3-3 :
   ∀ {i j} {A : Set i} {B : Set j} → 
   _≡_ {i ⊔ j} {(A × B) → (A × B)} (λ {(a , b) → ((first (a , b)) , (second (a , b)))}) (λ {(a , b) → (a , b)})
  lemma3-3 = refl
  -}

  {-
  lemma3 : (lemma2 ∘ lemma1) ≡ id
  lemma3 = proof
   where
    {-
    lemma3-0 : lemma1 ≡ (λ p → (λ b → (if b then (first p) else (second p))))
    lemma3-0 = refl
    
    
    lemma3-1 : (lemma2 ∘ lemma1) ≡ (λ p → (lemma2 (λ b → if b then (first p) else (second p))))
    lemma3-1 = refl
    -}

    {-
    lemma3-2 :
      (lemma2 ∘ lemma1) ≡ 
      (λ {(a , b) → 
       (
        (first (a , b)) ,
        (second (a , b))
       )
      })
    lemma3-2 = refl
    -}


    {-
    lemma3-3 : ∀ {i j} (A : Set i) (B : Set j) → (p : A × B) → p ≡ (first p , second p)
    lemma3-3 {i} {j} A B (a , b) = refl

    lemma3-4 : ∀ {i j} (A : Set i) (B : Set j) → (f g : A → B) → f ≡ g → (λ x → (f x)) ≡ (λ x → (g x))
    lemma3-4 {i} {j} A B f .f refl = refl
    -}
    {-
    lemma3-5 : (λ p → (first p) , (second p)) ≡ (λ {(a , b) → ((first (a , b)) , (second (a , b)))})
    lemma3-5 = refl 
    -}

    proof = refl 
    -}
    -- Use trees for exponentials instead??
    
  -- ??
  -- http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.90.2386 

 module FunctionalSets where
  open BaseDefinitions.Product
  open BaseDefinitions.Equality.Definition
  open Functions.Predicates
  open PropositionalSets
  subset : ∀ {i} (A : Set i) → Set ((lsuc lzero) ⊔ i)
  subset {i} A = ∃ B ∈ Set , (∃ f ∈ (B → A) , (Injective f))


  -- how to do set operations with these?
  -- one way is to map them to Subset where we have the operations already defined:
  subset→Subset : ∀ {i} {A : Set i} → subset A → Subset A
  subset→Subset {i} {A} (B , (f , f-inj)) a = ∃ b ∈ B , ((f b) ≡ a)

  {-
  _⊆_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A ⊆ B = ∃ f ∈ (A → B) , (Injective f) 
  -}
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


-----------------------------------------------------------------------------------------
module Cardinality where
 {-
 -- bijection as 1-1 correspondence; 
 -- existence of 1-1 correspondence of elements as same cardinality
 -- is an equivalence relation
 -- https://en.wikipedia.org/wiki/Finite_set#Necessary_and_sufficient_conditions_for_finiteness
 
 -- correspondence to some natural number
 -- correspondence to Fin; bijection with Fin
 -- listability
 -- every non-empty subset of S has a least and greatest element
 -- countability vs. uncountability; cantor's theorem
 -- A is finite  iff  for all B subset of A, f:A->B is a bijection implies A=B.
 -- Kuratowski finiteness
 -- S can be given a total ordering which is well-ordered both forwards and backwards
 -- Every surjective function from S onto itself is 1-1
 -- S is empty or every partial ordering of S contains a maximal element
 -- Dedekind infiniteness: the existence of a bijection between it and some proper subset of itself
-}

{-
    I-finite. Every non-empty set of subsets of S has a ⊆-maximal element. 
         This is equivalent to requiring the existence of a ⊆-minimal element. 
         It is also equivalent to the standard numerical concept of finiteness.

    Ia-finite. For every partition of S into two sets, at least one of the two sets is I-finite.

    II-finite. Every non-empty ⊆-monotone set of subsets of S has a ⊆-maximal element.

    III-finite. The power set P(S) is Dedekind finite.

    IV-finite. S is Dedekind finite.

    V-finite. ∣S∣ = 0 or 2⋅∣S∣ > ∣S|.

    VI-finite. ∣S∣ = 0 or ∣S∣ = 1 or ∣S∣2 > ∣S∣.

    VII-finite. S is I-finite or not well-orderable.
-}

{-
Definitions of Finiteness based on order properties
http://h.web.umkc.edu/halle/PapersForEveryone/Dofboop.pdf
-}
 
 ---------------------------------------------------------------------------------------
 module Cardinality₁ where
  open Functions.Predicates
  open Functions.Bijections
  open Sets.PropositionalSets
  
  Cardinality : ∀ {i} → Set i → Set i → Set i
  Cardinality {i} A = mkEquiv A (_hasBijectionWith_) Bij-equiv

 module Cardinality₂ where
  open BaseDefinitions.Equality.Definition
  open Equality.Properties
  open BaseDefinitions.Product
  open Functions.Predicates
  open Functions.Inverses.FunctionInverses
  open Functions.Bijections
  open Cardinality₁ renaming (Cardinality to TypeCardinality)

  -- note the generalizations of injectivity and surjectivity
  Cardinality : ∀ {i} {A : Set i} → (S : A → Set i) → Set i → Set i
  Cardinality {i} {A} S B = ∃ f ∈ (B → A) , ((f isInjective) ∧ ((b : B) → S (f b)) ∧ ((a : A) → S a → ∃ b ∈ B , ((f b) ≡ a)))

  Cardinality-lemma : ∀ {i} {A : Set i} → (S : A → Set i) → (B B' : Set i) → Cardinality S B → Cardinality S B' → TypeCardinality B B'
  Cardinality-lemma {i} {A} S B B' (f , (f-inj , (f-embedding , f-covering))) (g , (g-inj , (g-embedding , g-covering))) =  (h₁ , h₁-bij)
   where
    h₁ : B → B'
    h₁ b = π₁ (g-covering (f b) (f-embedding b))

    h₁-lemma1 : (b : B) → S (f b)
    h₁-lemma1 b = f-embedding b

    h₁-lemma2 : (b : B) → ∃ b* ∈ B' , ((g b*) ≡ (f b))
    h₁-lemma2 b = g-covering (f b) (f-embedding b)

    h₂ : (b : B) → (g (h₁ b)) ≡ (f b)
    h₂ b = π₂ (g-covering (f b) (f-embedding b))

    h₁' : B' → B
    h₁' b' = π₁ (f-covering (g b') (g-embedding b'))

    h₁'-lemma1 : (b' : B') → S (g b')
    h₁'-lemma1 b' = g-embedding b'

    h₁'-lemma2 : (b' : B') → ∃ b'* ∈ B , ((f b'*) ≡ (g b'))
    h₁'-lemma2 b' = f-covering (g b') (g-embedding b')

    h₂' : (b' : B') → (f (h₁' b')) ≡ (g b')
    h₂' b' = π₂ (f-covering (g b') (g-embedding b'))

    h'h-inv : h₁' isInverseOfₑ h₁
    h'h-inv = (h'h-Linv , h'h-Rinv)
     where
      h'h-Linv : (h₁' isLInverseOfₑ h₁)
      h'h-Linv x = h'hx=x
       where
        ghx=fx : (g (h₁ x)) ≡ (f x)
        ghx=fx = h₂ x
 
        fh'hx=ghx : (f (h₁' (h₁ x))) ≡ g (h₁ x)
        fh'hx=ghx = h₂' (h₁ x)
        
        h'hx=x = f-inj (≡-trans fh'hx=ghx ghx=fx) 
      h'h-Rinv : (h₁' isRInverseOfₑ h₁)
      h'h-Rinv x = hh'x=x
       where
        fh'x=gx : (f (h₁' x)) ≡ (g x)
        fh'x=gx = h₂' x

        ghh'x=fh'x : (g (h₁ (h₁' x))) ≡ (f (h₁' x))
        ghh'x=fh'x = h₂ (h₁' x)
        
        hh'x=x = g-inj (≡-trans ghh'x=fh'x fh'x=gx)
        
    h₁-bij : h₁ isBijective
    h₁-bij = π₁ (Inv-bij h₁ (h₁' , h'h-inv))
  
      
 module Finiteness where
  module I-finiteness where
   open BaseDefinitions.Product
   open Sets.PropositionalSets
   -- Every non-empty set of subsets of S has a ⊆-maximal element.
   -- Define:
    -- subsets of A
      -- A → Set ?
      -- A → Bool ?
      -- A' → A?
    -- set of subsets
    -- ⊆ relation between subsets
    -- ⊆-maximality property
    -- ⊆ defines a partial order
   Finite : ∀ {i j k} → (A : Set i) → Set (i ⊔ ((lsuc j) ⊔ (lsuc k)))
   Finite {i} {j} {k} A =
     (P : (A → Set j) → Set k) →                                                       -- for every set of subsets of A, P
     (∃ s ∈ (A → Set j) , (P s)) →                                                    -- P non-empty
     (∃ M ∈ (A → Set j) , ((P M) ∧ ((M' : A → Set j) → (P M') → (M' ⊆ M))))        -- P contains ⊆-maximal element

   

  module Ia-finiteness where
   open I-finiteness
   -- For every partition of S into two sets, at least one of the two sets is I-finite.
   

  module II-finiteness where

  module III-finiteness where
   -- The power set P(S) is Dedekind finite.
   -- how to properly define the powerset for this purpose?
   -- A → Bool *should* behave like powerset?
   -- With Bools you can basically case-match on the possible outputs
   -- but no function extensionality!
   -- use trees for power-set?

  module IV-finiteness where
   -- Dedekind infiniteness: the existence of a bijection between it and some proper subset of itself
   open Functions.Predicates renaming (Injective to _isEmbedding; Surjective to _isCovering)
   Finite : ∀ {i} (A : Set i) → Set i
   Finite A = (f : A → A) → f isEmbedding → f isCovering
 

  module V-finiteness where
  -- ∣S∣ = 0 or 2⋅∣S∣ > ∣S|.
  -- how to characterize 2·|S| and |S₁| > |S₂| ?
  -- |A| ≤ |B| iff exists injection A → B ?
  -- |A| ≤ |B| iff exists surjection B → A ?
    -- no, because no surjection from inhabited sets to the empty set
  -- |A| = |B| iff exists injection A → B ∧ injection B → A ?
  -- |A| = |B| iff exists injection A → B ∧ surjection A → B ?
    


  module VI-finiteness where

  module VII-finiteness where
   open I-finiteness
   
   
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
   -- we don't need values to occur in the List uniquely; non-uniqueness does not affect the determination of finteness
   

  module FinFiniteness where
   open BaseDefinitions.Product
   open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
   open BaseDefinitions.BaseTypes.Fin
   open Functions.Predicates

   Finite : ∀ {i} (A : Set i) → Set i
   Finite A = ∃ n ∈ ℕ , (∃ f ∈ (Fin n → A) , Bijective f)
   

 module Special where
  open BaseDefinitions.Product
  open BaseDefinitions.Negation.Definition
  open BaseDefinitions.Equality.Definition
  -- empty
  Empty : ∀ {i} (A : Set i) → Set i
  Empty A = ¬ A
  -- bijection with Fin 0
  -- injection to Singletons
  -- no surjection to Singletons
  -- no injection from Singletons
  -- no surjection from Singletons
  
  -- singleton
  Singleton : ∀ {i} (A : Set i) → Set i
  Singleton A = ∃ x ∈ A , ((y : A) → x ≡ y)
 -- n element
  -- Fin n ?
 -- aleph_0 = first countable infinity = size of Nat
 -- cardinality of continuum = size of Real
 
-- correspondence between finite cardinalities and individual natural numbers
-- 

module Geometry where
 open BaseDefinitions.Void
 open BaseDefinitions.Equality.Definition
 open Equality.Properties
 open BaseDefinitions.Product
 open BaseDefinitions.Nat renaming (Nat to ℕ)
 open BaseArithmetic.Operations hiding (_+_)
 open BaseArithmetic.Results
 open Sets.PropositionalSets
 open Cardinality.Cardinality₂ renaming (Cardinality to SetCardinality)
 open BaseDefinitions.Fin
 open BaseArithmetic.FinOperations

 Point : Set
 Point = ℕ × ℕ


 Grid-metric : Point → Point → ℕ 
 Grid-metric (a , b) (a' , b') = (diff a a') + (diff b b')
 --inherently non-zero

 {-
 Grid-metric-IoI : (p q : Grid) → (Grid-metric p q) ≡ 0 → p ≡ q
 Grid-metric-IoI (0       , 0      ) (0        , 0       ) refl = refl
 Grid-metric-IoI (x       , 0      ) (y        , (suc b')) p    = ω (sx≠0 p)
 Grid-metric-IoI (x       , (suc b)) (y        , 0       ) p    = ω (sx≠0 p)
 Grid-metric-IoI ((suc a) , x      ) (0        , y       ) p    = ω (sx≠0 (≡-trans (≡-sym (sx+y=x+sy a (diff x y))) p)) --  (+-comm (suc a) (diff x y)))))
 Grid-metric-IoI (0       , x      ) ((suc a') , y       ) p    = ω (sx≠0 (≡-trans (≡-sym (sx+y=x+sy a' (diff x y))) p))
 Grid-metric-IoI (0       , (suc b)) (0        , (suc b')) p    = ∧-≡-lemma refl (cong suc (cong second (Grid-metric-IoI (0 , b) (0 , b') p)))
 Grid-metric-IoI ((suc a) , 0      ) ((suc a') , 0       ) p    = ∧-≡-lemma (cong suc (cong first (Grid-metric-IoI (a , 0) (a' , 0) p))) refl
 Grid-metric-IoI ((suc a) , (suc b)) ((suc a') , (suc b')) p    = proof
  where
   ab=a'b' : (a , b) ≡ (a' , b')
   ab=a'b' = Grid-metric-IoI (a , b) (a' , b') p
   a=a'    = cong first ab=a'b'
   b=b'    = cong second ab=a'b'
   sa=sa'  = cong suc a=a'
   sb=sb'  = cong suc b=b'
   proof   = ∧-≡-lemma sa=sa' sb=sb'
  -}


 {-
 Grid-metric-IoI₂ : (p q : Grid) → p ≡ q → (Grid-metric p q) ≡ 0
 Grid-metric-IoI₂ (a , b) (.a , .b) p = ≡-trans (cong (_+_ (diff a a')) (cong second p)) (cong (λ q → 0 + q) (cong 
 -}

 Grid-metric-comm : (p q : Point) → (Grid-metric p q) ≡ (Grid-metric q p)
 Grid-metric-comm (a , b) (a' , b') = ≡-trans (cong (λ q → q + (diff b b')) (diff-comm a a')) (cong (_+_ (diff a' a)) (diff-comm b b'))

 {-
 Grid-metric-triangle : (x y z : Point) → 
 -}

 -- equivalence classes of sets by cardinality
 -- equivalence classes by cardinality partitions any set-level
 -- so we need a Cardinality type
  -- the Cardinality of a Type will be the equivalence class of that set wrt the 
  -- the Cardinality of a Set will be the 

 -- needs *a lot* more work
 data Grid-measure : (Point → Set) → ℕ → Set₁ where
  empty : Grid-measure (λ p → ⊥) 0
  singleton : {p : Point} → Grid-measure ([ p ]) 1
  union : {S T : Point → Set} {m n : ℕ} → (Grid-measure S m) → (Grid-measure T n) → (Grid-measure (S ∪ T) (m + n))

 Grid-measure₁ : (ℕ → Set) → Set → Set
 Grid-measure₁ S B = SetCardinality S B

 -- prove that this satisfies the definition of a measure
 Interval : ℕ → (ℕ → Set)
 Interval n = λ m → m < n

 {-
 m[Interval] : (n : ℕ) → SetCardinality (Interval n) (Fin n)
 m[Interval] n = Fin[n]→ℕ , (Fin[n]→ℕ-inj , (Fin[n]→ℕ-embedding , Fin[n]→ℕ-covering))
  where
   Fin[n]→ℕ : Fin n → ℕ
   Fin[n]→ℕ zero = 0
   Fin[n]→ℕ (suc n) = suc (Fin[n]→ℕ (Fin[n]→Fin[n+1] n))
   
   Fin[n]→ℕ-inj : {x y : Fin n} → (Fin[n]→ℕ x) ≡ (Fin[n]→ℕ y) → x ≡ y
   Fin[n]→ℕ-inj {zero} {zero} p = refl
   Fin[n]→ℕ-inj {zero} {suc y} ()
   Fin[n]→ℕ-inj {suc x} {zero} ()
   Fin[n]→ℕ-inj {suc x} {suc y} p = proof
    where
     proof
   
   Fin[n]→ℕ-embedding : (x : Fin n) → (Fin[n]→ℕ x) < n
   Fin[n]→ℕ-embedding {x} = proof
    where
     proof

   Fin[n]→ℕ-covering : (m : ℕ) → m < n → ∃ x ∈ (Fin n) , ((Fin[n]→ℕ x) ≡ m)
   Fin[n]→ℕ-covering m (k , m+sk=n) = (x , fx=m)
    where
     x
     fx=m
 -}
 -- ∃ f ∈ (B → A) , ((f isInjective) ∧ ((b : B) → S (f b)) ∧ ((a : A) → S a → ∃ b ∈ B , ((f b) ≡ a)))


 {-
 Grid-measure₂ : (Point → Set) → Set → Set
 Grid-measure₂ S B = SetCardinality S B
 -}

 -- length of a path through ℕ × ℕ by way of metric
 -- length of a path through ℕ × ℕ by way of measure
 -- equivalence of these definitions of path-length
 

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
 open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
 open BaseArithmetic.BooleanPredicates
 open BaseDefinitions.BaseTypes.List
 open Boolean.Operations renaming (_eq_ to Bool-eq)
 open Containers.Maybe.Definition
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
   
   UnlabeledToLabeled : TransitionSystem → LabeledTransitionSystem  
   UnlabeledToLabeled T = record {S = S; L = ⊤; ⇒ = (λ p a q → ⇒ p q)}
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

  -- "internal" / "unobservable" actions
    -- how to formulate this notion?
  -- weak bisimulation equivalence
    -- Hennessy Milner Logic
    -- relation to logical equivalence
  -- strong bisimulation equivalence
    -- sensitive to "internal actions"
  -- trace equivalence
    -- doesn't preserve deadlock properties

  --relational definition of bisimulation
  --fixed-point definition of bisimulation
    -- how to talk about least and greatest fixed points?
    -- just like lcm and gcd..; universal properties in general;
      -- there's a function, f : A → A
      -- there's a partial order, _≤_ : A → A → Set
      -- there's a fixedpoint; x = f x
      -- and its the least/greatest one relative to the order:
      -- ∀ y : A, (y = f x) → x ≤ y
  --game-theoretical definition of bisimulation
  --coalgebraic definition of bisimulation
  --Simulation preorder

  --transitive closure: →*
  --inverse relation
     -- same as converse relation?
  --composition of relations
  --reflexive symmetric transitive closure
  --joinability
    -- reflexive
    -- symmetric
    -- transitive ?
  --church-rosser property
  --church-rosser theorem for LC
  --confluence
  --semi-confluence
  --local/weak confluence
  --Theorem: Church-Rosser property ≡ confluent ≡ semi-confluent
  --terminating/Noetherian
  --convergent: confluent + terminating
  --counterexample showing local/weak confluence ≠ confluence:
     {-
       b→c
       c→b
       b→a
       c→d
     -}
  --Newman's lemma
    -- Huet's proof using well-founded induction
  
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
     δ : (∃ q ∈ Q , ¬ (F q)) × Γ → Q × (Γ × Bool)
     -- note: subset theory
     -- set-theoretic complement:
       -- Σ-no-b : ¬ (Σ b)
       -- (∃ q ∈ Q , ¬ (F q))
     -- Q not necessarily finite
       -- but q₀ ensures it's non-empty
     -- Γ not necessarily finite
       -- but b ensures it's non-empty
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
 -}
-------------------------------------------------------------------
 {-
 Finite state machine
 -}
 module FiniteStateAutomaton where
  open BaseDefinitions.Product
  open BaseDefinitions.BaseTypes.Nat renaming (Nat to ℕ)
  open BaseDefinitions.BaseTypes.Fin
  open BaseArithmetic.FinOperations
  module DFA1 where
   record DFA : Set₁ where
    field
     Q : Set                         -- set of states Q
                                       -- must be finite
                                       -- non-emptiness guaranteed by q₀
     Σ : Set                         -- input alphabet
                                       -- must be finite
                                       -- must be non-empty
     q₀ : Q
     F : Q → Set                     -- accepting states
     δ : Q × Σ → Q
   module DFAProperties where
    open BaseDefinitions.Equality.Definition
    open TransitionSystem.LabeledTransitionSystem1
    DFA→LTS : DFA → LabeledTransitionSystem
    DFA→LTS dfa = record { S = Q ; L = Σ ; ⇒ = λ x l x' → (δ (x , l) ≡ x)}
     where
      open DFA dfa
  module DFA2 where
   record DFA : Set where
    field
     Q : ℕ
     Σ : ℕ
     q₀ : Fin (suc Q)
     F : Fin (suc Q)
     δ : (Fin (suc Q)) × (Fin (suc Σ)) → (Fin (suc Q))
   -- semiautomata

   module DFAProperties where
    open BaseArithmetic.BinaryPredicates
    open DFA1 renaming (DFA to DFA1)
    DFA→DFA1 : DFA → DFA1
    DFA→DFA1 dfa =
     record{
      Q = Fin (suc Q) ;
      Σ = Fin (suc Σ) ;
      q₀ = q₀ ;
      F = λ q → ℕ[ q ] ≤ ℕ[ F ] ;
      δ = δ
     }
     where
      open DFA dfa
  module MealyMachines where
   module MealyMachine1 where
    record MealyMachine : Set₁ where
     field
      Q : Set                    -- states
                                   -- must be finite
                                   -- non-emptiness ensured by q₀
      Σ : Set                    -- input alphabet
                                   -- must be finite
                                   -- must be non-empty
      Γ : Set                    -- output alphabet
                                   -- must be finite
                                   -- must be non-empty
      q₀ : Q                     -- start state
      δ : Q × Σ → Q             -- state-transition function
      ω : Q × Σ → Γ             -- output function

   module MealyMachine2 where
    record MealyMachine : Set₁ where
     field
      Q : Set

  module MooreMachines where
   module MooreMachine1 where
    record MooreMachine : Set₁ where
     field
      Q : Set
      Σ : Set
      Γ : Set
      q₀ : Q
      δ : Q × Σ → Q
      ω : Q → Γ
   {-
   module MooreMachine2 where
    record MooreMachine : Set₁ where
     field
      Q : Set
      Q-fin : Finite Q
      q₀ : Q
      Σ : Set
      Σ-fin : Finite Σ
      Σ₀ : Σ
      Γ : Set
      Γ-fin : Finite Γ
   -} 
      

  module MooreToMealy where
   open MealyMachines.MealyMachine1
   open MooreMachines.MooreMachine1
   Moore→Mealy : MooreMachine → MealyMachine
   Moore→Mealy moore =
    record{
     Q = Q ;
     Σ = Σ ;
     Γ = Γ ;
     q₀ = q₀ ;
     δ = δ ;
     ω = λ p → ω (first p)
    }
    where
     open MooreMachine moore
     
  module MealyToMoore where
   {-
   Mealy→Moore : MealyMachine → MooreMachine
   Mealy→Moore mealy =  
    record {
     Q = Q ;
     Σ = Σ ;
     Γ = Γ ;
     q₀ = q₀ ;
    } 
   -}

  -- equivalence of mealy & moore machines
  -- constructing mealy & moore machines by attaching an output function to a semiautomaton.
  -- Equivalence to NDFAs
  -- closure under:
   -- union
   -- intersection
   -- concatenations
   -- negation
   -- Kleene closure
   -- Reversal
   -- Init
   -- Quotient
   -- Substitution
   -- Homomorphism
  -- recognizing regular languages /  regexes
  -- DFA minimization
    -- hopcroft minimization algorithm
  -- inability of DFA to recognize Dyck/parentheses language
  -- Mealy machines
  -- Moore machines
  -- UML state machines
    -- as in Unified Modeling Language
  -- SDL state machines
    -- as in Specification and Description Language

 {-
 Turing completeness
 Unsolvability of halting problem by Turing machines
 -}

{-
Resistor
Semiconductor
 n-type
 p-type
Transistor
Diode
DTL := Diode-Transistor Logic
TTL := Transistor-Transistor Logic
RTL := Resistor-Transistor Logic
Bipolar junction transistor
 NPN
 PNP
Field-effect transistor
https://en.wikipedia.org/wiki/Reversible_computing
XOR gate: non-reversible
CNOT := controlled-NOT gate; reversible
https://en.wikipedia.org/wiki/Toffoli_gate
* any reversible gate can be implemented on a quantum computer
https://en.wikipedia.org/wiki/McEliece_cryptosystem

Belt-machine
Mill architecture

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

---------------------------------------------------
{-
Algebraic data-types
Generalized algebraic data-types
Inductive types
Induction-recursion
Induction-induction
Coinductive types

Inductive types as least fixed-points
Coinductive types as greatest fixed-points
https://cstheory.stackexchange.com/questions/10594/whats-the-difference-between-adts-gadts-and-inductive-types#comment29078_10596
https://bartoszmilewski.com/2017/02/28/f-algebras/
 

-}

module Character where
 open BaseDefinitions.Product
 open BaseDefinitions.Equality.Definition
 open BaseDefinitions.Bool
 open Boolean.Operations
 open Boolean.Conversions
 open Boolean.Complex
 open BaseDefinitions.Nat
 open BaseArithmetic.Operations
 open BaseDefinitions.Vector
 open Containers.Vector.BooleanPredicates
 open Containers.Maybe.Definition
 open Containers.Maybe.BooleanPredicates
 open Containers.Maybe.Complex

 -- there is a primitive Char data-type but it's wrong; Chars are not a philosophically primitive data-type
 Char : Set
 Char = Vector Bool 8

 CharEq : Char → Char → Bool
 CharEq c d = VectorEq BoolEq c d

 CharToNat : {n : Nat} → Vector Bool n →  Nat
 CharToNat [] = 0
 CharToNat {n} (b ∷ bs) = ((boolToNat b) * (2 ^ n)) + (CharToNat bs)

 Char≤ : {n : Nat} → Vector Bool n → Vector Bool n → Bool
 Char≤ [] [] = true
 Char≤ (true ∷ v) (true ∷ w) = Char≤ v w
 Char≤ (true ∷ v) (false ∷ w) = false
 Char≤ (false ∷ v) (true ∷ w) = true
 Char≤ (false ∷ v) (false ∷ w) = Char≤ v w

 NatEq : Nat → Nat → Bool
 NatEq 0 0 = true
 NatEq (suc n) 0 = false
 NatEq 0 (suc m) = false
 NatEq (suc n) (suc m) = NatEq n m

 Nat≤ : Nat → Nat → Bool
 Nat≤ 0 0 = true
 Nat≤ 0 (suc n) = true
 Nat≤ (suc n) 0 = false
 Nat≤ (suc n) (suc m) = Nat≤ n m

 zeroVec : (n : Nat) → Vector Bool n
 zeroVec 0 = []
 zeroVec (suc n) = false ∷ (zeroVec n)

 incWithCarry : {n : Nat} → Vector Bool n → (Vector Bool n) × Bool
 incWithCarry [] = [] , true
 incWithCarry (b ∷ bs) = (r ∷ rs) , c
  where
   bs' = incWithCarry bs
   rs = first bs'
   t = halfAdd b (second bs')
   r = first t
   c = second t
 
 inc : {n : Nat} → Vector Bool n → Vector Bool n
 inc v = first (incWithCarry v)

 NatToChar : Nat → Maybe Char
 NatToChar n = NatToCharHelper n 256 (zeroVec 8)
  where
   NatToCharHelper : Nat → Nat → Char → Maybe Char
   NatToCharHelper 0       n c = Just c
   NatToCharHelper (suc n) 0 c = Nothing
   NatToCharHelper (suc n) (suc m) c = NatToCharHelper n m (inc c)


 QMARK  = extractMaybe (NatToChar 63) refl
 SPACE  = extractMaybe (NatToChar 32) refl
 LPAREN = extractMaybe (NatToChar 40) refl
 RPAREN = extractMaybe (NatToChar 41) refl

 {-
 Punctuation : Nat × Nat
 Punctuation = 
 -}

 Numeric : Nat × Nat
 Numeric = 48 , 57

 AlphaUpper : Nat × Nat
 AlphaUpper = 65 , 90

 AlphaLower : Nat × Nat
 AlphaLower = 97 , 122

 mkRange : Nat × Nat → Maybe (Vector Bool 8 → Bool)
 mkRange (m , n) =
  if (Nat≤ m n) then
   (dite (checkMaybe (NatToChar m))
   (λ p → (dite (checkMaybe (NatToChar n))
   (λ q → Just (λ c → (Char≤ (extractMaybe (NatToChar m) p) c) and (Char≤ c (extractMaybe (NatToChar n) q))))
   (λ q → Nothing)))
   (λ p → Nothing))
  else Nothing

 isAlphaUpper = extractMaybe (mkRange AlphaUpper) refl
 isAlphaLower = extractMaybe (mkRange AlphaLower) refl
 isAlpha = λ x → (isAlphaUpper x) or (isAlphaLower x)
 isNumeric = extractMaybe (mkRange Numeric) refl
 isAlphaNumeric = λ x → (isAlpha x) or (isNumeric x)


module String where
 open BaseDefinitions.Bool
 open BaseDefinitions.List
 open Containers.List.BooleanPredicates
 open Character
 
 String : Set
 String = List Char

 StringEq : String → String → Bool
 StringEq s t = ListEq CharEq s t


module ContextFreeGrammar where
 open BaseDefinitions.Product
 open BaseDefinitions.Sum
 open BaseDefinitions.Bool
 open Boolean.Operations
 open BaseDefinitions.List
 open Containers.List.Operations
 open BaseDefinitions.Unit
 open Containers.Maybe.Definition
 open Character
 data NonTerminal : Set where
  START : NonTerminal
  TOKEN : NonTerminal
  TERM  : NonTerminal
  WS    : NonTerminal

 NTEq : NonTerminal → NonTerminal → Bool
 NTEq START START = true
 NTEq TOKEN TOKEN = true
 NTEq TERM  TERM  = true
 NTEq WS    WS    = true
 NTEq x     y     = false

 Grammar : Set
 Grammar = List (NonTerminal × (List (List (Char ∨ NonTerminal))))

 {-
 myGrammar : Grammar
 myGrammar = 
  (START , (((inr WS) ∷ []) ∷ ((inr TOKEN) ∷ []) ∷ ((inr TERM)  ∷ (inr START) ∷ []) ∷ [])) ∷
  (TOKEN , (((inr CHAR) ∷ []) ∷ ((inr CHAR)  ∷ (inr TOKEN) ∷ []) ∷ [])) ∷
  (WS    , (((inl SPACE) ∷ []) ∷ ((inl SPACE) ∷ (inr WS) ∷ []) ∷ [])) ∷
  (TERM  , (((inl LPAREN) ∷ (inr START) ∷ (inl RPAREN) ∷ []) ∷ [])) ∷ 
  []
 -}
 RHS : Set
 RHS = List ((Char ∨ ⊤) × (List (Char ∨ NonTerminal)))

 Grammar₂ : Set
 Grammar₂ = List (NonTerminal × RHS)

 -- Greibach Normal Form
 Grammar₃ : Set
 Grammar₃ = RHS × Grammar₂

 prepGrammar₂ : Grammar₂ → Maybe Grammar₃
 prepGrammar₂ [] = Nothing
 prepGrammar₂ (r ∷ rs) = Just ((second r) , (r ∷ rs))

 LRecRHS : Set
 LRecRHS = List (List (Char ∨ NonTerminal))

 matchChar : Char → RHS → LRecRHS
 matchChar c [] = []
 matchChar c (((inl d) , rhs) ∷ rest) = if (CharEq c d) then (rhs ∷ (matchChar c rest)) else (matchChar c rest) 
 matchChar c (((inr unit), rhs) ∷ rest) = (rhs ∷ (matchChar c rest))

 lookUp : NonTerminal → Grammar₂ → RHS
 lookUp NT [] = []
 lookUp NT ((NT₂ , rhs) ∷ rest) = (if (NTEq NT NT₂) then rhs else []) ++ (lookUp NT rest)

 expand : LRecRHS → Grammar₂ → RHS
 expand [] g = []
 expand ([] ∷ restOptions) g = expand restOptions g
 expand (((inl c) ∷ restOption) ∷ restOptions) g = ((inl c) , restOption) ∷ (expand restOptions g)
 expand (((inr NT) ∷ restOption) ∷ restOptions) g = (map (λ q → (first q) , ((second q) ++ restOption)) (lookUp NT g)) ++ (expand restOptions g)

 derivative : Char → Grammar₃ → Grammar₃
 derivative c ([] , []) = ([] , [])
 derivative c ([] , g) = ([] , g)
 derivative c (q  , []) = ([] , [])
 derivative c ((q ∷ qs)  , g) = (expand (matchChar c (q ∷ qs)) g) , g 

 {-
 START = " " WS START | ALPHANUM TOKEN | "(" TERM
 TOKEN = ALPHANUM  | ALPHANUM TOKEN
 WS    = " " | " " WS
 TERM  = " " WS START ")" | ALPHANUM TOKEN ")" | "(" TERM ")"
 -}


 {-
 derivative : Grammar₂ → Char → Grammar₂
 derivative
 dSTART/dSPACE =  START -> START 
                ~ START -> " " START | c START | "(" START
 dTERM/dSPACE = TERM -> START ")"
              ~ TERM -> " " START ")" | 
 
 -}
 {-
 START -> WS START | TOKEN | TOKEN WS | TOKEN WS START | TERM | TERM WS | TERM START
 TOKEN -> CHAR | CHAR TOKEN
 WS    -> " "  | " " WS
 TERM  -> "(" START ")" 
 -}
 

 {-
 myGrammar₂ : Grammar₂
 myGrammar₂ =
     (START , (
               ∷ ((inl SPACE ) , ((inr START) ∷ []))
               ∷ ((inl LPAREN) , ((inr TERM)  ∷ []))
               ∷ ((inr unit  ) , [])
               ∷ ((inr unit  ) , ((inr TOKEN) ∷ []))
               ∷ ((inr unit  ) , ((inr TOKEN) ∷ (inr WS) ∷ (inr START) ∷ []))
               ∷ ((inl LPAREN) , ((inr TERM)  ∷ (inr START) ∷ []))
               ∷ []
               )
     )
                  
  ∷ (TOKEN , (   ((inr unit  ) , [])                 
               ∷ ((inr unit  ) , ((inr TOKEN) ∷ []))
               ∷ []
               )
     )

  ∷ (WS ,    (   ((inl SPACE ) , [])
               ∷ ((inl SPACE ) , ((inr WS) ∷ []))
               ∷ []
              )
     )
               
  ∷ (TERM  , (
                  ((inl SPACE  ) , ((inr WS   ) ∷ (inl RPAREN) ∷ []))
               ∷ ((inr unit   ) , ((inr TOKEN) ∷ (inl RPAREN) ∷ []))
               ∷ ((inl LPAREN ) , ((inr TERM ) ∷ (inl RPAREN) ∷ []))
               ∷ ((inl SPACE  ) , ((inr WS   ) ∷ (inr START ) ∷ (inl RPAREN) ∷ []))
               ∷ ((inr unit   ) , ((inr TOKEN) ∷ (inr START ) ∷ (inl RPAREN) ∷ [])) 
               ∷ ((inl LPAREN ) , ((inr TERM ) ∷ (inr START ) ∷ (inl RPAREN) ∷ []))
               ∷ []
              )
     )
  ∷ []
  -}
 
 
  
 -- reduction from CFG to non-left-recursive CFG
 -- you can trivially take the derivative of any context-free grammar that's not left-recursive
 -- 
 anyChar : List Char → Maybe Char
 anyChar [] = Nothing
 anyChar (c ∷ cs) = Just c

 parseToken : List Char → List Char
 parseToken [] = []
 parseToken (c ∷ cs) = if (isAlphaNumeric c) then (c ∷ (parseToken cs)) else []

 parseWS : List Char → List Char
 parseWS [] = []
 parseWS (c ∷ cs) = if (CharEq c SPACE) then (c ∷ (parseWS cs)) else []

 parseToken₂ : List Char → (List Char) × (List Char)
 parseToken₂ [] = [] , []
 parseToken₂ (c ∷ cs) = if (isAlphaNumeric c) then ((c ∷ (first (parseToken₂ cs))) , (second (parseToken₂ cs))) else ([] , cs)

 parseWS₂ : List Char → (List Char) × (List Char)
 parseWS₂ [] = [] , []
 parseWS₂ (c ∷ cs) = if (CharEq c SPACE) then ((c ∷ (first (parseWS₂ cs))) , (second (parseWS₂ cs))) else ([] , cs)

 {-
 -- derivative of a parser wrt a character is a new parser
 -- derivative of 
 -}


module ListOperations where
 open BaseDefinitions.Levels
 open BaseDefinitions.Void
 open BaseDefinitions.Negation
 open BaseDefinitions.Unit
 open BaseDefinitions.Bool
 open BaseDefinitions.Nat renaming (suc to _+1)
 open BaseDefinitions.Fin renaming (suc to _+1)
 open BaseDefinitions.List
 open BaseDefinitions.Equality.Definition
 open BaseDefinitions.Sum
 open BaseDefinitions.Product
 open BaseDefinitions.Biimplication.Definition
 open BaseDefinitions.Negation.Definition
 open Boolean.Operations
 open Boolean.Complex
 open BaseArithmetic.FinOperations
 open BaseArithmetic.BooleanPredicates
 open BaseArithmetic.Results renaming (𝕤x≰0 to x+1≰0 ; sx≤sy→x≤y to x+1≤y+1→x≤y ; x≤y→sx≤sy to x≤y→x+1≤y+1 ; x<y→sx<sy to x<y→x+1<y+1)
 open Equality.Properties
 open Containers.List
 open Containers.List.Operations
 open Orders
 open Decidability
 open Functions.Special
 open Functions.Composition.Definition
 
 ∧-map : ∀ {i j k l} {A : Set i} {B : Set j} {A' : Set k} {B' : Set l} → (A → A') → (B → B') → A ∧ B → A' ∧ B'
 ∧-map f g (a , b) = f a , g b

 _∈_ : ∀ {i} {A : Set i} → A → List A → Set i
 x ∈ []        = Lift ⊥ 
 x ∈ (a ∷ as) = (x ≡ a) ∨ (x ∈ as)

 ListIn : ∀ {i} {A : Set i} → A → List A → Set i
 ListIn x l = foldr (_∨_ ∘ (_≡_ x)) (Lift ⊥) l

 ListIn₂ : ∀ {i} {A : Set i} → A → List A → Set i
 ListIn₂ x l = ∃ n ∈ (Fin (length l)) , ((l < n >) ≡ x)

 ⊥-∨-lemma : ∀ {i} {A : Set i} → A ∨ ⊥ → A
 ⊥-∨-lemma {i} {A} (inl a) = a
 ⊥-∨-lemma {i} {A} (inr ())

 ListIn₂-lemma : ∀ {i} {A : Set i} (l : List A) (n : Fin (length l)) (x : A) → ((l < n >) ≡ ((x ∷ l) < n +1 >))
 ListIn₂-lemma []        ()
 ListIn₂-lemma (a ∷ as) n    x = refl

 {-
 ∈-lemma : ∀ {i} {A : Set i} → (x : A) → (l : List A) → 
 -}

 {-
 ∈→ListIn₂ : ∀ {i} {A : Set i} → (x : A) → (l : List A) → x ∈ l → ListIn₂ x l
 ∈→ListIn₂ x [] ()
 ∈→ListIn₂ x (a ∷ as) (inl p) = (zero , (≡-sym p))
 ∈→ListIn₂ x (a ∷ as) (inr p) = ∧-map _+1 id (∈→ListIn₂ x as p)
 -}
 {-
  where
   recurse = ∈→ListIn₂ x as p
 -}
 {-
 ListIn→ListIn₂ : ∀ {i} {A : Set i} → (x : A) → (l : List A) → ListIn x l → ListIn₂ x l
 ListIn→ListIn₂ x []        ()
 ListIn→ListIn₂ x (a ∷ as) (inl p) = (zero , (≡-sym p))
 ListIn→ListIn₂ x (a ∷ as) (inr p) = (((first recurse) +1) , second recurse)
  where
   recurse : ListIn₂ x as
   recurse = ListIn→ListIn₂ x as p
 -}
 {-
   first recurse : Fin (length as)
   second recurse : as < (first recurse) > ≡ x
    
 -}

 {-
 _∈_,_times : ∀ {i} {A : Set i} → A → List A → Set i
 x ∈ₙ l ,      0 times = ¬ (x ∈ l)
 x ∈ₙ l , (n +1) times = 
 -}

 SameSet : ∀ {i} {A : Set i} → (l1 l2 : List A) → Set i
 SameSet {i} {A} l1 l2 = (x : A) → (x ∈ l1) ↔ (x ∈ l2)

 {-
 SameMultiset : ∀ {i} {A : Set i} → (l1 l2 : List A) → Set i
 SameMultiset {i} {A} l1 l2 = 
 -}

 SameList : ∀ {i} {A : Set i} → (l1 l2 : List A) → Set i
 SameList []        []          = Lift ⊤
 SameList []        (a' ∷ as') = Lift ⊥
 SameList (a ∷ as) []          = Lift ⊥
 SameList (a ∷ as) (a' ∷ as') = (a ≡ a') ∧ (SameList as as')


 filter : ∀ {i} {A : Set i} → List A → (A → Bool) → List A
 filter []        F = []
 filter (a ∷ as) F = if (F a) then (filter as F) else (a ∷ (filter as F))

 prefix : ∀ {i} {A : Set i} → (l : List A) → Fin ((length l) +1) → List A
 prefix l         zero    = []
 prefix []        (() +1)
 prefix (a ∷ as) (n +1) = a ∷ (prefix as n)

 {-
 suffix : ∀ {i} {A : Set i} → (l : List A) → Fin ((length l) +1) → List A
 suffix l         zero    = []
 suffix (a ∷ as) (n +1) = a ∷ 
 -}

 _<∶_> : ∀ {i} {A : Set i} → (l : List A) → (end : Fin ((length l) +1)) → List A
 l <∶ end > = prefix l end

 
 _<_∶> : ∀ {i} {A : Set i} → (l : List A) → (start : Fin ((length l) +1)) → List A
 l         < zero  ∶> = l
 []        < () +1 ∶>
 (a ∷ as) < n +1  ∶> = as < n ∶>

 
 _<_∶_>-helper_ : ∀ {i} {A : Set i} → (l : List A) → (start end : Fin ((length l) +1)) → ((Fin→Nat start) ≤ (Fin→Nat end)) → List A
 l         < zero  ∶ y    >-helper 0≤y = l <∶ y >
 []        < () +1 ∶ y    >-helper ⁇
 (a ∷ as) < x +1  ∶ zero >-helper x+1≤0 = ω (x+1≰0 x+1≤0)
 (a ∷ as) < x +1  ∶ y +1 >-helper x+1≤y+1 = as < x ∶ y >-helper (x+1≤y+1→x≤y x+1≤y+1)

 converse : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → ¬ B → ¬ A
 converse f ¬B a = ¬B (f a)

 -- could also have done: process of elimination on the trichotomy
 x≰y→y<x : {x y : Nat} → ¬ (x ≤ y) → y < x
 x≰y→y<x {0}    {y}    0≰y     = ω (0≰y (0≤x y))
 x≰y→y<x {x +1} {0}    x+1≰0   = x , ≡-sym (x=0+x (x +1))
 x≰y→y<x {x +1} {y +1} x+1≰y+1 = x<y→x+1<y+1 {y} {x} (x≰y→y<x {x} {y} ((converse (x≤y→x+1≤y+1 {x} {y})) x+1≰y+1))

 lte-decides-≤ : _lte_ decides₂ _≤_
 lte-decides-≤ = sound , complete
  where
   sound : {x y : Nat} → (x lte y) ≡ true → x ≤ y
   sound {0} {y} refl = y , ≡-sym (x=0+x y)
   sound {x +1} {0} ()
   sound {x +1} {y +1} p = x≤y→x+1≤y+1 (sound {x} {y} p)
   
   complete : {x y : Nat} → x ≤ y → (x lte y) ≡ true
   complete {0}    {y}    0≤y     = refl
   complete {x +1} {0}    x+1≤0   = ω (x+1≰0 x+1≤0)
   complete {x +1} {y +1} x+1≤y+1 = complete (x+1≤y+1→x≤y x+1≤y+1)


 ¬[x=b]→x=not-b : {x b : Bool} → ¬ (x ≡ b) → x ≡ (not b)
 ¬[x=b]→x=not-b {true}  {true}  ¬[true=true]   = ω (¬[true=true] refl)
 ¬[x=b]→x=not-b {true}  {false} ¬[true=false]  = refl
 ¬[x=b]→x=not-b {false} {true}  ¬[false=true]  = refl
 ¬[x=b]→x=not-b {false} {false} ¬[false=false] = ω (¬[false=false] refl)

 x=not-b→¬[x=b] : {x b : Bool} → x ≡ (not b) → ¬ (x ≡ b)
 x=not-b→¬[x=b] {true} {true} ()
 x=not-b→¬[x=b] {true} {false} refl ()
 x=not-b→¬[x=b] {false} {true} refl ()
 x=not-b→¬[x=b] {false} {false} ()

 {-
 decides-converse : ∀ {i j} {A : Set i} {r : A → A → Bool} {R : A → A → Set j} → r decides₂ R → ({x y : Nat} → (r x y) ≡ false → ¬ (R x y)) ∧ ({x y : Nat} → ¬ (R x y) → (r x y) ≡ false)
 decides-converse {i} {j} {A} {r} {R} (r-sound , r-complete) = r-sound-conv , r-complete-conv
  where
   -- converse of 
   r-complete-conv : {x y : Nat} → (r x y) ≡ false → ¬ (R x y)s
   r-complete-conv {x} {y} p Rxy =
   
   r-sound-conv : {x y : Nat} → 
 -}

 length[x++y]=length[x]+length[y] : ∀ {i} {A : Set i} (x y : List A) → length (x ++ y) ≡ ((length x) + (length y))
 length[x++y]=length[x]+length[y] []        y = x=0+x (length y)
 length[x++y]=length[x]+length[y] (x ∷ xs) y = ≡-trans p1 p2
  where
   p1 = cong _+1 (length[x++y]=length[x]+length[y] xs y)
   p2 = x+sy=sx+y (length xs) (length y)
  {-
   length ((x ∷ xs) ++ y) ≡ ((length (x ∷ xs)) + (length y))
        ↕ refl                         ↕ refl
   length (x ∷ (xs ++ y))    (((length xs) +1) + (length y))
        ↕ refl                          ↑  x+sy=sx+y (length xs) (length y) 
   (length (xs ++ y)) +1      ((length xs) + ((length y) +1))
                                        ↕ refl
                              ((length xs) + (length y)) +1

   cong _+1 (length[x++y]=length[x]+length[y] xs y) : (length (xs ++ y)) ≡ ((length xs) + (length y))
  -}
 {-
 length[rev-l]=length[l] : ∀ {i} {A : Set i} (l : List A) → length (rev l) ≡ length l
 length[rev-l]=length[l] [] = refl
 length[rev-l]=length[l] (a ∷ as) = cong _+1 (length[rev-l]=length[l] as)
 -} 

 {-
 _<_∶_> : ∀ {i} {A : Set i} → (l : List A) → (x y : Fin ((length l) +1)) → List A
 _<_∶_> {i} {A} l x y =
  dite ((Fin→Nat x) lte (Fin→Nat y))
   true-branch
   false-branch
  where
   true-branch : ((Fin→Nat x) lte (Fin→Nat y)) ≡ true → List A
   true-branch t = l < x ∶ y >-helper ((first lte-decides-≤) t)

   false-branch : ((Fin→Nat x) lte (Fin→Nat y)) ≡ false → List A
   false-branch f = (rev ((rev l) < coerce y p ∶ coerce x p >-helper (≤-leq₂ (x≰y→y<x ((converse (second lte-decides-≤)) (x=not-b→¬[x=b] f))))))
    where
     p : Fin ((length (rev l)) +1) ≡ Fin ((length l) +1)
     p = cong (λ q → Fin (q +1)) (length[rev-l]=length[l] l)
 -}

 {-
 split : ∀ {i} {A : Set i} → List A → A → (A → A → Bool) → List (List A)
 split [] Δ _==_ = []
 split (a ∷ as) Δ _==_ = if (a == Δ) then 
 -}

 {-
 SortingFunction : ∀ {i} (A : Set i) (r : A → A → Bool) → TotalOrder A (λ x y → (r x y) ≡ true) → Set i
 SortingFunction {i} A r O = ∃ f ∈ (List A → Bool) , ((
 -}

 
 

module ModalRewriter where
 open BaseDefinitions.Product
 open BaseDefinitions.Sum
 open BaseDefinitions.Bool
 open BaseDefinitions.Equality.Definition
 open Equality.Properties
 open BaseDefinitions.List
 open Containers.List.Operations hiding (_<_>)
 open BaseDefinitions.Nat
 open BaseDefinitions.Vector
 open BaseDefinitions.Unit
 open Functions.Composition.Definition
 open Boolean.Operations
 open Boolean.Complex
 open Boolean.Conversions
 open BaseDefinitions.BaseTypes.Fin
 open BaseArithmetic
 open BaseArithmetic.Operations hiding (_+_)
 open BaseArithmetic.FinOperations hiding (_-_)
 open BaseArithmetic.Results
 open Containers.Maybe.Definition
 open Containers.Maybe.BooleanPredicates
 open Containers.Maybe.Complex
 open Containers.List.BooleanPredicates hiding (find)
 open Containers.Vector.BooleanPredicates hiding ([_])
 open Containers.BinTree hiding (store)
 open Character
 open String
 open Containers2.Vector.Operations renaming (remove to VectorRemove)

 -- rule = pair(input-pattern , output-pattern)
 -- ruleset = list of rules
 -- pick applicable rule
 -- queue semantics
 -- list of tokens
 -- parse string
 --

 data Token : Set where
  const : String → Token
  var : Nat → Token

 TokenEq : Token → Token → Bool
 TokenEq (const c) (const d) = StringEq c d
 TokenEq (const c) x         = false
 TokenEq (var   v) (var   w) = NatEq v w
 TokenEq (var   v) x         = false
  
 data AST : Set where
  token : Token → AST
  term : List AST → AST

 TermEqHelper : List AST → List AST → Bool
 TermEqHelper [] [] = true
 TermEqHelper (a ∷ as) [] = false
 TermEqHelper []        (b ∷ bs) = false
 TermEqHelper ((token t) ∷ rest) ((token u) ∷ rest2) = TokenEq t u
 TermEqHelper ((token t) ∷ rest) (x ∷ rest2)         = false
 TermEqHelper ((term as) ∷ rest) ((term bs) ∷ rest2) = (TermEqHelper as bs) and (TermEqHelper rest rest2)
 TermEqHelper ((term as) ∷ rest) (x ∷ rest2)         = false

 TermEq : AST → AST → Bool
 TermEq x y = TermEqHelper [ x ] [ y ]

 data AST₂ : Nat → Set where
  token : Token → AST₂ 0
  term : {n : Nat} → List (AST₂ n) → AST₂ (suc n)

 data AST₃ : Nat → Set where
  token : {n : Nat} → Token → AST₃ n
  term : {n : Nat} → List (AST₃ n) → AST₃ (suc n)

 addToken' : {n : Nat} → List Char → List AST → List AST
 addToken' [] ast = ast
 addToken' t  ast = ast ++ [ token (const t) ]

 addToken : {n : Nat} → List Char → Vector (List AST) (suc n) → Vector (List AST) (suc n)
 addToken [] ast = ast
 addToken t  (ast ∷ asts) = (ast ++ [ token (const t) ]) ∷ asts

 merge : { n : Nat} → Vector (List AST) (suc (suc n)) → Vector (List AST) (suc n)
 merge {n} (ast₁ ∷ ast₂ ∷ asts) = (ast₂ ++ [ term ast₁ ]) ∷ asts

 VecFirst : {A : Set} {n : Nat} → Vector A (suc n) → A
 VecFirst (a ∷ as) = a

 getTerm : Vector (List AST) 1 → AST
 getTerm ast = term (VecFirst ast)

 parseState : Nat → Set
 parseState n = List Char × Vector (List AST) (suc n)

 emptyState : parseState 0
 emptyState = ([] , ([] ∷ []))

 doLPAREN : {n : Nat} → parseState n → Maybe (parseState (suc n))
 doLPAREN (t , ast) = Just ([] , ([] ∷ (addToken t ast)))

 doRPAREN2 : {n : Nat} → parseState (suc n) → parseState n
 doRPAREN2 {n} (t , ast) = [] , (merge (addToken t ast))

 doRPAREN : {n : Nat} → parseState n → Maybe (parseState (n - 1))
 doRPAREN {0}     s     = Nothing
 doRPAREN {suc n} s     = coerce (Just (doRPAREN-sub s)) (cong (λ q → Maybe (parseState q)) (n=n-0 n))
  where
   doRPAREN-sub : {m : Nat} → parseState (suc m) → parseState m
   doRPAREN-sub (t , ast) = [] , (merge (addToken t ast))

 doSPACE : {n : Nat} → parseState n → Maybe (parseState n)
 doSPACE (t , ast) = Just ([] , (addToken t ast))

 doCHAR : {n : Nat} → Char → parseState n → Maybe (parseState n)
 doCHAR c (t , ast) = Just ((t ++ [ c ]) , ast)
 



 -- not the best parser
 -- put them in in reverse order and then just reverse once
 parse : {n : Nat} → List Char → parseState n → Maybe AST
 parse {0}       []       ([] , ([] ∷ [])) = Nothing
 parse {0}       []       (t , ast)         = Just (getTerm (addToken t ast))
 parse {(suc n)} []       state             = Nothing
 parse {n}       (c ∷ x) state             =
  dite
  (checkMaybe (π₂ nextState))
  (λ p → (parse x (extractMaybe (π₂ nextState) p)))
  (λ p → Nothing)
   where
     nextState : ∃ m ∈ Nat , (Maybe (parseState m))
     nextState =
      if         (CharEq c LPAREN) then ((n + 1)    , (doLPAREN state))
       else (if  (CharEq c RPAREN) then ((n - 1)    , (doRPAREN state))
        else (if (CharEq c SPACE ) then (n          , (doSPACE  state))
         else                           (n          , (doCHAR   c state))
      ))

 
 parseInput : List Char → Maybe AST
 parseInput s = parse s emptyState
 

 
 -- disjoint-set roots either: point to some term, or point back to themselves
 -- could alternatively have the vars themselves be trees as in unifying-variables
  -- this is really the underlying data-structure that union-find exploits;
 find-check : {A : Set} {n : Nat} → Vector Bool n → (A ∨ (Vector Bool n)) → Bool
 find-check v (inl a) = true
 find-check v (inr w) = VectorEq BoolEq v w

 {-
 find-helper2 : {A : Set} {n : Nat} → Vector Bool n → (A ∨ (Vector Bool n)) → 
 -}

 find-checkLemma : {A : Set} {n : Nat} → (v : Vector Bool n) → (p : (A ∨ (Vector Bool n))) → (find-check v p) ≡ false → ∃ w ∈ (Vector Bool n) , (p ≡ (inr w))
 find-checkLemma {A} {n} v (inl a) ()
 find-checkLemma {A} {n} v (inr w) p = w , refl


 find-checkLemma2 : {A : Set} {n : Nat} → (v : Vector Bool n) → (s : (BinTree (A ∨ (Vector Bool n)) n)) → (find-check v (retrieve s v)) ≡ false → ∃ w ∈ (Vector Bool n) , ((retrieve s v) ≡ (inr w))
 find-checkLemma2 {A} {n} v s p = find-checkLemma v (retrieve s v) p

 check-inl : ∀ {i j} {A : Set i} {B : Set j} → A ∨ B → Bool
 check-inl (inl a) = true
 check-inl (inr b) = false

 check-inr : ∀ {i j} {A : Set i} {B : Set j} → A ∨ B → Bool
 check-inr (inl a) = false
 check-inr (inr b) = true

 extract-inl : ∀ {i j} {A : Set i} {B : Set j} → (p : A ∨ B) → (check-inl p) ≡ true → A
 extract-inl (inl a) p = a
 extract-inl (inr b) ()

 extract-inr : ∀ {i j} {A : Set i} {B : Set j} → (p : A ∨ B) → (check-inr p) ≡ true → B
 extract-inr (inl a) ()
 extract-inr (inr b) p = b
 

 find-helper : {A : Set} {n : Nat} → BinTree (A ∨ (Vector Bool n)) n → Vector Bool n → List (Vector Bool n) → Nat → Maybe ((Vector Bool n) × (List (Vector Bool n)))
 find-helper s v l 0 = Nothing
 find-helper s v l (suc n) =
  -- check if the retrieved node is a root (constant or self-pointing var), otherwise retrieve again
  dite (find-check v (retrieve s v))
   (λ p → (Just (v , l)))
   (λ p → (find-helper s (π₁ (find-checkLemma2 v s p)) (v ∷ l) n))
 
 binTree-find : {A : Set} {n : Nat} → BinTree (A ∨ (Vector Bool n)) n → Vector Bool n → Maybe ((Vector Bool n) × (List (Vector Bool n)))
 binTree-find {A} {n} s v = find-helper s v [] (2 ^ n)

 union-helper : {A : Set} {n : Nat} (f : A → A → A) → (a b : A ∨ (Vector Bool n)) → A ∨ (Vector Bool n)
 union-helper {A} f (inl a) (inl b) = inl (f a b)
 union-helper {A} f (inl a) (inr w) = inl a
 union-helper {A} f (inr v) (inl b) = inl b
 union-helper {A} f (inr v) (inr w) = inr v

 {-
 p = (binTree-find s v) q = (binTree-find s w)
 first p    <---  first q
 union-helper _++_ (retrieve s p) (retrieve s q) <--- first p
 -}

 {-
 union₂ : {m n : Nat} → BinTree ((List (AST₃ m)) ∨ (Vector Bool n)) n → (v w : Vector Bool n) → BinTree ((List (AST₃ m)) ∨ (Vector Bool n)) n
 union₂ s v w = store (store s ((retrieve s v) ++ (retrieve s w))) w (inr v)
 -} 
 module Dictionary where
  Dictionary : ∀ {i j} (A : Set i) (B : Set j) (R : A → A → Bool) → Set (i ⊔ j)
  Dictionary {i} {j} A B R = List (A × B)

  lookup : ∀ {i j} {A : Set i} {B : Set j} {R : A → A → Bool} → Dictionary A B R → A → Maybe B
  lookup []                x = Nothing
  lookup {R = R} ((a , b) ∷ rest) x = if (R x a) then (Just b) else (lookup {R = R} rest x)

  add : ∀ {i j} {A : Set i} {B : Set j} {R : A → A → Bool} → Dictionary A B R → A → B → Dictionary A B R
  add []                x y = (x , y) ∷ []
  add {R = R} ((a , b) ∷ rest) x y = if (R x a) then ((x , y) ∷ rest) else (add {R = R} rest x y)

  remove : ∀ {i j} {A : Set i} {B : Set j} {R : A → A → Bool} → Dictionary A B R → A → Dictionary A B R
  remove [] a = []
  remove {R = R} ((a , b) ∷ rest) x = if (R x a) then rest else ((a , b) ∷ (remove {R = R} rest x))

 
  removeAll : ∀ {i j} {A : Set i} {B : Set j} {R : A → A → Bool} → Dictionary A B R → A → Dictionary A B R
  removeAll [] a = []
  removeAll {R = R} ((a , b) ∷ rest) x = (if (R x a) then [] else [ (a , b) ]) ++ (remove {R = R} rest x)
 
 module Dictionary₂ where
  Dictionary : ∀ {i j} (A : Set i) (B : Set j) (R : A → A → Bool) (n : Nat) → Set (i ⊔ j)
  Dictionary A B R n = Vector (A × B) n

  {-
  lookup : ∀ {i j} {A : Set i} {B : Set j} {R : A → A → Bool} {n : Nat} → Dictionary A B R n → A → Maybe B
  lookup [] a = Nothing
  lookup {R = R} ((a , b) ∷ rest) x = if (R x a) then (Just b) else (lookup {R = R} rest x)
  -}

  lookup : ∀ {i j} {A : Set i} {B : Set j} {R : A → A → Bool} {n : Nat} → Dictionary A B R n → A → Maybe (Fin n)
  lookup [] a = Nothing
  lookup {R = R} ((a , b) ∷ rest) x =
   if (R x a) then
     (Just zero)
   else (
    (λ lookupRest → 
      dite (checkMaybe lookupRest)
      (λ t → Just (suc (extractMaybe lookupRest t))) 
      (λ f → Nothing)
    ) (lookup {R = R} rest x) 
   )
  

  storeConditional : ∀ {i j} {A : Set i} {B : Set j} {R : A → A → Bool} {n : Nat} → Dictionary A B R n → A → B → Dictionary A B R n
  storeConditional [] x y = []
  storeConditional {R = R} ((a , b) ∷ rest) x y = if (R x a) then ((x , y) ∷ rest) else ((a , b) ∷ (storeConditional {R = R} rest x y))
 

  remove : ∀ {i j} {A : Set i} {B : Set j} {R : A → A → Bool} {n : Nat} → Dictionary A B R (suc n) → Fin (suc n) → Dictionary A B R n
  remove = VectorRemove



  addDefinite :
   ∀ {i j} {A : Set i} {B : Set j} {R : A → A → Bool} {n : Nat} →
   Dictionary A B R n →
   A →
   B →
   Dictionary A B R (suc n)
  
  addDefinite d x b = (x , b) ∷ d

 

 module PointerDictionary where
  open Dictionary
  
  PointerDictionary : ∀ {i j} (A : Set i) (B : Set j) (R : A → A → Bool) → Set (i ⊔ j)
  PointerDictionary {i} {j} A B R = Dictionary A (A ∨ B) R

 -- tries and acyclic DFAs


 module PointerDictionary₂ where
  open Dictionary₂
  
  PointerDictionary : ∀ {i j} (A : Set i) (B : Set j) (R : A → A → Bool) (n : Nat) → Set (i ⊔ j)
  PointerDictionary {i} {j} A B R n = Dictionary A (A ∨ B) R n

 -- what a mess!
 -- we can clean it up syntactically quite a bit
 -- we can simplify at least somewhat by getting rid of the check for the inr case, i.e.
 -- we're just traversing pointers between vars and not considering the constants/terms they're bound to until later
 -- notice how it throws away the return values from recursions until the very end
 {-
 find(d : Dictionary , x : Key)

 lookup-x = lookup d x
 if (checkMaybe(lookup-x)) {        
  x-index = extractMaybe(lookup-x)
  x-value = second(d[x])

  if (check-inl(x-value)) {                -- inl for pointers; inr for values
   key = x-value.inl
   recurse = find(d.remove(x-index),key) 

   if (x == key){
    Just x-index
   }
   else {
    if (check-maybe recurse) {
     
    }else {
     Nothing
    }
   }
  }
  else (Just x-index) 
 } 
 else Nothing

 -}
 
  find : ∀ {i j} {A : Set i} {B : Set j} {R : A → A → Bool} {n : Nat} → PointerDictionary A B R n → A → Maybe (Fin n)
  find {n = 0}             [] x = Nothing
  find {R = R} {n = suc n} d  x =
   (λ lookup-x → 
    dite (checkMaybe lookup-x)
     (λ t →
      (λ x-index →
       dite (check-inl (second (d < x-index >)))
        (λ t₂ →
         (λ key → 
          dite (R x key)
           (λ t₃ → Just x-index)
           (λ f →
             (λ recurse →
              dite (checkMaybe recurse)
               (λ t₄ → Just (Fin[n]→Fin[n+1] (extractMaybe recurse t₄)))
               (λ f → Nothing)
             ) (find {R = R} {n = n} (remove {R = R} d x-index) key)
           )
         ) (extract-inl (second (d < x-index >)) t₂)
        )
        (λ f → Just x-index)
      )
      (extractMaybe lookup-x t)
     )
    
     (λ f → Nothing)
   ) (lookup {R = R} d x)

 module PointerDictionary₃ where
  PointerDictionary : ∀ {i} (A : Set i) (n : Nat) → Set i
  PointerDictionary A n = Vector ((Fin n) ∨ A) n

 module PointerDictionary₄ where
  open Dictionary₂
  
  PointerDictionary : ∀ {i j} (A : Set i) (B : Set j) (R : A → A → Bool) (n : Nat) → Set (i ⊔ j)
  PointerDictionary A B R n = Dictionary A (A × Maybe B) R n 

  find : ∀ {i j} {A : Set i} {B : Set j} {R : A → A → Bool} {n : Nat} → PointerDictionary A B R n → A → Maybe A
  find         {n = 0}     [] x = Nothing
  find {i = i} {j = j} {R = R} {n = suc n} d  x = 
   (λ lookup-x → 
    dite (checkMaybe lookup-x)
     (λ t →
      (λ x-index →
       (λ key → 
        dite (R x key)
         (λ t₂ → Just x)
         (λ f → 
          (λ recurse →
           dite (checkMaybe recurse)
            (λ t₃ → Just (extractMaybe recurse t₃))
            (λ f → Nothing)
          ) (find {R = R} {n = n} (remove {R = R} d x-index) key)
         )
       ) (first (second (d < x-index >)))
      ) (extractMaybe lookup-x t)
    )
    (λ f → Nothing)
   ) (lookup {R = R} d x)

 module BinTrie₁ where
  open Boolean.Conversions
  open Containers.Maybe.Operations
  
  data BinTrie {i} (A : Set i) : (depth nodes : Nat) → Set i where
   leaf : A → BinTrie A 0 1
   left : {d n : Nat} → BinTrie A d n → BinTrie A (d + 1) n                          -- left for false
   right : {d n : Nat} → BinTrie A d n → BinTrie A (d + 1) n                         -- right for true
   both : {d m n : Nat} → BinTrie A d m → BinTrie A d n → BinTrie A (d + 1) (m + n)

  _∈_ : ∀ {i} {A : Set i} {depth nodes : Nat} → Vector Bool depth → BinTrie A depth nodes → Bool
  []              ∈ (leaf x)   = true
  (true  ∷ rest) ∈ (right t)  = rest ∈ t
  (false ∷ rest) ∈ (right t)  = false
  (true  ∷ rest) ∈ (left t)   = false
  (false ∷ rest) ∈ (left t)   = rest ∈ t
  (true  ∷ rest) ∈ (both f t) = rest ∈ t
  (false ∷ rest) ∈ (both f t) = rest ∈ f

  size : ∀ {i} {A : Set i} {depth n : Nat} → BinTrie A depth n → Nat
  size {n = n} d = n

  mkTrie : ∀ {i} {A : Set i} {depth : Nat} → Vector Bool depth → A → BinTrie A depth 1
  mkTrie {i} {A} {depth = 0}     []              x = leaf x
  mkTrie {i} {A} {depth = suc n} (false ∷ rest) x = left (mkTrie rest x)
  mkTrie {i} {A} {depth = suc n} (true  ∷ rest) x = right (mkTrie rest x)

  store : ∀ {i} {A : Set i} {depth nodes : Nat} → (d : BinTrie A depth nodes) → (v : Vector Bool depth) → A → BinTrie A depth (nodes + (boolToNat (not (v ∈ d))))
  store {i} {A} {depth = 0}     {nodes} (leaf  a)   []              x = leaf x
  store {i} {A} {depth = suc n} {nodes} (left  f)   (false ∷ rest) x = left (store f rest x)
  store {i} {A} {depth = suc n} {nodes} (left  f)   (true  ∷ rest) x = both f (mkTrie rest x)
  store {i} {A} {depth = suc n} {nodes} (right t)   (false ∷ rest) x = coerce (both (mkTrie rest x) t) p
   where
    p : (BinTrie A (suc n) (1 + nodes)) ≡ (BinTrie A (suc n) (nodes + 1))
    p = cong (BinTrie A (suc n)) (+-comm 1 nodes)
  store {i} {A} {depth = suc n} {nodes} (right t)   (true  ∷ rest) x = right (store t rest x)
  store {i} {A} {depth = suc n} {nodes} (both  f t) (false ∷ rest) x = coerce (both (store f rest x) t) p
   where
    N[f] = size f
    N[t] = size t
    Δ = boolToNat (not (rest ∈ f))
    p : (BinTrie A (suc n) ((N[f] + Δ) + N[t])) ≡ (BinTrie A (suc n) ((N[f] + N[t]) + Δ))
    p = cong (BinTrie A (suc n)) q
     where
      q : ((N[f] + Δ) + N[t]) ≡ ((N[f] + N[t]) + Δ)
      q = ≡-trans r (≡-trans s u) 
       where
        r : ((N[f] + Δ) + N[t]) ≡ (N[f] + (Δ + N[t]))
        r = ≡-sym (+-assoc N[f] Δ N[t])

        s : (N[f] + (Δ + N[t])) ≡ (N[f] + (N[t] + Δ))
        s = cong (_+_ N[f]) (+-comm Δ N[t])

        u : (N[f] + (N[t] + Δ)) ≡ ((N[f] + N[t]) + Δ)
        u = +-assoc N[f] N[t] Δ
        
  store {i} {A} {depth = suc n} {nodes} (both  f t) (true  ∷ rest) x = coerce (both f (store t rest x)) p
   where
    p = cong (BinTrie A (suc n)) (+-assoc (size f) (size t) (boolToNat (not (rest ∈ t))))  

  lookup : ∀ {i} {A : Set i} {depth nodes : Nat} → BinTrie A depth nodes → Vector Bool depth → Maybe A
  lookup (leaf x) [] = Just x
  lookup (left L) (false ∷ rest) = lookup L rest
  lookup (left L) (true ∷ rest) = Nothing
  lookup (right R) (false ∷ rest) = Nothing
  lookup (right R) (true ∷ rest) = lookup R rest
  lookup (both L R) (false ∷ rest) = lookup L rest
  lookup (both L R) (true ∷ rest) = lookup R rest

  {-
  remove : ∀ {i} {A : Set i} {depth nodes : Nat} → (d : BinTrie A depth nodes) → (v : Vector Bool depth) → Maybe (BinTrie A depth (nodes - (boolToNat (v ∈ d))))
  remove (leaf x) [] = Nothing
  remove (left L) (false ∷ rest) = MaybeMap left (remove L rest)
  remove {i} {A} {depth} {nodes} (left L) (true ∷ rest) = coerce (Just (left L)) p
   where
    p = cong (λ q → Maybe (BinTrie A depth q)) r
     where
      r : nodes ≡ (nodes - 0)
      r = n=n-0 nodes
  remove {i} {A} {depth} {nodes} (right R) (false ∷ rest) = coerce (Just (right R)) p
   where
    p = cong (λ q → Maybe (BinTrie A depth q)) r
     where
      r : nodes ≡ (nodes - 0)
      r = n=n-0 nodes
  remove (right R) (true ∷ rest) = MaybeMap right (remove R rest)
  remove {i} {A} {depth} {nodes} (both L R) (false ∷ rest) =
   Just (
    dite (checkMaybe (remove L rest))
     (λ t → both (extractMaybe (remove L rest) t) R)
     (λ f → coerce (right R) p)
   )
   where
    x+y=z → z-x=y
    sizeL = 1
    sizeR = size R
    p = cong (BinTrie A depth) r
     where
      r : 
  remove (both L R) (true ∷ rest) =
   Just (
    dite (checkMaybe (remove R rest))
     (λ t → both L (extractMaybe (remove R rest) t))
     (λ f → left L)
   )
  -}
  
 module BinTrie₂ where
  open Containers.Maybe.Operations
  
  data BinTrie {i} (A : Set i) : (depth : Nat) → Set i where
   leaf : A → BinTrie A 0
   left : {n : Nat} → BinTrie A n → BinTrie A (n + 1)
   right : {n : Nat} → BinTrie A n → BinTrie A (n + 1)
   both : {n : Nat} → BinTrie A n → BinTrie A n → BinTrie A (n + 1)
 
  size : ∀ {i} {A : Set i} {depth : Nat} → BinTrie A depth → Nat
  size (leaf x) = 1
  size (left L) = size L
  size (right R) = size R
  size (both L R) = (size L) + (size R)

  _∈_ : ∀ {i} {A : Set i} {depth : Nat} → Vector Bool depth → BinTrie A depth → Bool
  []              ∈ (leaf  x)   = true
  (false ∷ rest) ∈ (left  L)   = rest ∈ L
  (false ∷ rest) ∈ (right R)   = false
  (false ∷ rest) ∈ (both  L R) = rest ∈ L
  (true  ∷ rest) ∈ (left  L)   = false
  (true  ∷ rest) ∈ (right R)   = rest ∈ R
  (true  ∷ rest) ∈ (both  L R) = rest ∈ R

  mkTrie : ∀ {i} {A : Set i} {n : Nat} → Vector Bool n → A → BinTrie A n
  mkTrie []              x = (leaf x)
  mkTrie (false ∷ rest) x = left  (mkTrie rest x)
  mkTrie (true  ∷ rest) x = right (mkTrie rest x)

  store : ∀ {i} {A : Set i} {n : Nat} → BinTrie A n → Vector Bool n → A → BinTrie A n
  store (leaf  a)   []              x = leaf x
  store (left  L)   (false ∷ rest) x = left (store L rest x)
  store (left  L)   (true  ∷ rest) x = both L (mkTrie rest x)
  store (right R)   (false ∷ rest) x = both (mkTrie rest x)  R
  store (right R)   (true  ∷ rest) x = right (store R rest x)
  store (both  L R) (false ∷ rest) x = both L (store R rest x)
  store (both  L R) (true  ∷ rest) x = both (store R rest x) R

  lookup : ∀ {i} {A : Set i} {n : Nat} → BinTrie A n → Vector Bool n → Maybe A
  lookup (leaf a) [] = Just a
  lookup (left L) (false ∷ rest) = lookup L rest
  lookup (left L) (true  ∷ rest) = Nothing
  lookup (right R) (false ∷ rest) = Nothing
  lookup (right R) (true ∷ rest) = lookup R rest
  lookup (both L R) (false ∷ rest) = lookup L rest
  lookup (both L R) (true ∷ rest) = lookup R rest

  remove : ∀ {i} {A : Set i} {n : Nat} → BinTrie A n → Vector Bool n → Maybe (BinTrie A n)
  remove (leaf  x)   []              = Nothing
  remove (left  L)   (false ∷ rest) = MaybeMap left (remove L rest)
  remove (left  L)   (true  ∷ rest) = Just (left L)
  remove (right R)   (false ∷ rest) = Just (right R)
  remove (right R)   (true  ∷ rest) = MaybeMap right (remove R rest)
  remove (both  L R) (false ∷ rest) =
   Just (
    dite (checkMaybe (remove L rest))
     (λ t → both (extractMaybe (remove L rest) t) R)
     (λ f → right R)
   )
  remove (both  L R) (true  ∷ rest) =
   Just (
    dite (checkMaybe (remove R rest))
     (λ t → both L (extractMaybe (remove R rest) t))
     (λ f → left L)
   )

 module BinTrie₁,₂ where
  open BinTrie₁ renaming (BinTrie to BinTrie₁ ; size to size₁)
  open BinTrie₂ renaming (BinTrie to BinTrie₂ ; size to size₂)

  BinTrie₁→BinTrie₂ : ∀ {i} {A : Set i} {depth nodes : Nat} → BinTrie₁ A depth nodes → BinTrie₂ A depth
  BinTrie₁→BinTrie₂ (leaf x) = leaf x
  BinTrie₁→BinTrie₂ (left L) = left (BinTrie₁→BinTrie₂ L)
  BinTrie₁→BinTrie₂ (right R) = right (BinTrie₁→BinTrie₂ R)
  BinTrie₁→BinTrie₂ (both L R) = both (BinTrie₁→BinTrie₂ L) (BinTrie₁→BinTrie₂ R)

  BinTrie₂→BinTrie₁ : ∀ {i} {A : Set i} {depth : Nat} → (T : BinTrie₂ A depth) → BinTrie₁ A depth (size₂ T)
  BinTrie₂→BinTrie₁ (leaf x) = leaf x
  BinTrie₂→BinTrie₁ (left L) = left (BinTrie₂→BinTrie₁ L)
  BinTrie₂→BinTrie₁ (right R) = right (BinTrie₂→BinTrie₁ R)
  BinTrie₂→BinTrie₁ (both L R) = both (BinTrie₂→BinTrie₁ L) (BinTrie₂→BinTrie₁ R)

 module PointerDictionary₅ where
  open BinTrie₁
    
  PointerDictionary : ∀ {i} (A : Set i) (depth nodes : Nat) → Set i
  PointerDictionary {i} A d n = BinTrie ((Vector Bool d) × (Maybe A)) d n


 module PointerDictionary₆ where
  open BinTrie₂

  PointerDictionary : ∀ {i} (A : Set i) (depth : Nat) → Set i
  PointerDictionary {i} A d = BinTrie ((Vector Bool d) × (Maybe A)) d

  {-
  find : ∀ {i} {A : Set i} {depth : Nat} → PointerDictionary A depth → Vector Bool depth → Maybe (Vector Bool depth)
  find T k = MaybeMap f (lookup T k)
  -}

  {-
  find-helper : {i} {A : Set i} {depth : Nat} → (d : PointerDictionary A depth) → Vector Bool depth → ∃ n ∈ Nat , ((size d) ≡ n) → Maybe (Vector Bool depth)
  find-helper {i} {A : Set i} 

  find : ∀ {i} {A : Set i} {depth : Nat} → PointerDictionary A depth → Vector Bool depth → Maybe (Vector Bool depth)
  find
  -}
 {-
 -- when a var binds with another var you wanna union their trees and have one point to the other for future references
 -- m ]=]' 
 match-layer :
  {m n : Nat} →
  List (AST₃ m) →
  List (AST₃ m) →
  BinTree ((List (AST₃ m)) ∨ (Vector Bool n)) n →
  Maybe (BinTree ((List (AST₃ m)) ∨ (Vector Bool n)) n)
 match-layer {m} {n} []                        []                         s = Just s
 match-layer {m} {n} ((token (var v)) ∷ rest) (x ∷ rest2)               s = match-layer rest rest2 (bind v x s)
 match-layer {m} {n} (x ∷ rest)               ((token (var v)) ∷ rest2) s = match-layer rest rest2 (bind v x s)
 match-layer {(suc m)} {n} ((term as) ∷ rest) ((term bs) ∷ rest2)       s = match-layer rest rest2 (match-layer as bs s)
 match-layer {m} {n} ((token c) ∷ rest)       ((token d) ∷ rest2)       s = if (StringEq c d) then (Just s) else Nothing
 match-layer {m} {n} x                         y                          s = Nothing
 -}
 

 {-
 bind : {n : Nat} → Nat → AST → BinTree AST n → Maybe AST
 bind {n} m ast s = 

 -- recurse on the depth of the ASTs
 -- recurse on the number of variables
 match-helper : {n : Nat} → List AST → List AST → BinTree AST n → Maybe (BinTree AST n)
 match-helper []                           []                           s  = Just s
 match-helper ((token (var v)) ∷ rest)    (x ∷ rest2)                 s  = match-helper rest rest2 (bind v x s)
 match-helper (x ∷ rest)                  ((token (var v)) ∷ rest2)   s  = match-helper rest rest2 (bind v x s)
 match-helper ((term as)
 ∷ rest1)         ((term bs) ∷ rest2)         s  = match-helper rest1 rest2 (match-helper as bs s)
 match-helper ((token (const c)) ∷ rest1) ((token (const d)) ∷ rest2) s  = if (StringEq c d) then (Just s) else Nothing
 match-helper x                            y                            s  = Nothing
 -}


 -- serialize like unlambda; treat @ as special constant
 -- first check all constants
  -- loop over 
 -- then do all constant-var bindings
 
 
 -- then do all var ` bindings
 
 {-
 match : AST → AST → Maybe Substitution
 match ast₁ ast₂ = match-helper ast₁ ast₂ id
 -}
 {-
 -- https://en.wikipedia.org/wiki/Queue_(abstract_data_type)
 data QueueOp : Set where
  enqueue : QueueOp
  dequeue : QueueOp
 -}
 enqueue : {A : Set} → A → List A → List A
 enqueue a l = l ++ [ a ]

 dequeue : {A : Set} → List A → (List A) × (Maybe A)
 dequeue [] = ([] , Nothing)
 dequeue (a ∷ as) = (as , (Just a))


-- https://www.reddit.com/r/haskell/comments/cczju/coq_verification_of_some_of_okasakis_purely/

-- Lightweight Semiformal Time Complexity Analysis for Purely Functional Data Structures
-- Nils Anders Danielsson
-- http://www.cse.chalmers.se/~nad//publications/danielsson-popl2008.html
