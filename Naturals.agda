module Naturals where
  {-
    --------
    zero : ℕ

    m : ℕ
    ---------
    suc m : ℕ
  -}
  data ℕ : Set where -- inductive definition
      zero : ℕ       -- base case
      suc  : ℕ → ℕ   -- inductive case
    
  {-
    Inference rule

    a (judgment, hypothesis)
    ------
    b (judgment, conclusion)
  -}

  {-# BUILTIN NATURAL ℕ #-}

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

  _+_ : ℕ → ℕ → ℕ
  zero    + n = n
  (suc m) + n = suc (m + n)

  {-
    0       + n  ≡  n           zero is a left identity
    (1 + m) + n  ≡  1 + (m + n) addition is associative (m + n) + p  ≡  m + (n + p)
  -}

  _ : 2 + 3 ≡ 5
  _ =
    begin
      2 + 3
    ≡⟨⟩
      suc (1 + 3)
    ≡⟨⟩
      suc (suc (0 + 3))
    ≡⟨⟩
      suc (suc 3)
    ≡⟨⟩
      5
    ∎
    
  _ : 3 + 4 ≡ 7
  _ =
    begin
      3 + 4
    ≡⟨⟩ -- inductive
      suc (2 + 4)
    ≡⟨⟩ -- inductive
      suc (suc (1 + 4))
    ≡⟨⟩ -- inductive
      suc (suc (suc (0 + 4)))
    ≡⟨⟩ -- base
      suc (suc (suc 4))
    ≡⟨⟩ -- simplify
      7
    ∎

  _ : 3 + 4 ≡ 7
  _ = refl -- agda can do all of that for us

  _*_ : ℕ → ℕ → ℕ
  zero    * n = zero
  (suc m) * n = n + (m * n)

  {-
    0       * n  ≡  0           zero is a left annihilator
    (1 + m) * n  ≡  n + (m * n) multiplication distributes over addition (m + n) * p  ≡  (m * p) + (n * p) and 1 is a left identity for multiplication
  -}

  -- _ : 2 * 3 ≡ 6
  _ =
    begin
      2 * 3
    ≡⟨⟩    -- inductive case
      3 + (1 * 3)
    ≡⟨⟩    -- inductive case
      3 + (3 + (0 * 3))
    ≡⟨⟩    -- base case
      3 + (3 + 0)
    ≡⟨⟩    -- simplify
      6
    ∎

  _ =
    begin
      3 * 4
    ≡⟨⟩    -- inductive case
      4 + (2 * 4)
    ≡⟨⟩    -- inductive case
      4 + (4 + (1 * 4))
    ≡⟨⟩    -- inductive case
      4 + (4 + (4 + (0 * 4)))
    ≡⟨⟩    -- base case
      4 + (4 + (4 + 0))
    ≡⟨⟩    -- simplify
      12
    ∎
    
  _^_ : ℕ → ℕ → ℕ
  m ^ zero    = suc zero
  m ^ (suc n) = m * (m ^ n)

  {-
    m ^ 0        =  1
    m ^ (1 + n)  =  m * (m ^ n)
  -}

  _ : 3 ^ 4 ≡ 81
  _ =
    begin
      3 ^ 4
    ≡⟨⟩
      3 * (3 ^ 3)
    ≡⟨⟩
      3 * (3 * (3 ^ 2))
    ≡⟨⟩
      3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩
      3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩
      3 * (3 * (3 * (3 * 1)))
    ≡⟨⟩
      81
    ∎

  _ : 3 ^ 4 ≡ 81
  _ = refl
  
  _ : 3 ^ 4 ≡ 81
  _ =
    begin
      3 ^ 4
    ≡⟨⟩ -- ^ inductive
      3 * (3 ^ 3)
    ≡⟨⟩ -- ^ inductive
      3 * (3 * (3 ^ 2))
    ≡⟨⟩ -- ^ inductive
      3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩ -- ^ inductive
      3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩ -- ^ base
      3 * (3 * (3 * (3 * 1)))
    ≡⟨⟩ -- * inductive
      3 * (3 * (3 * (1 + (2 * 1))))
    ≡⟨⟩ -- * inductive
      3 * (3 * (3 * (1 + (1 + (1 * 1)))))
    ≡⟨⟩ -- * inductive
      3 * (3 * (3 * (1 + (1 + (1 + (0 * 1))))))
    ≡⟨⟩ -- * base
      3 * (3 * (3 * (1 + (1 + (1 + 0)))))
    ≡⟨⟩ -- + inductive
      3 * (3 * (3 * (1 + (1 + (suc (0 + 0))))))
    ≡⟨⟩ -- + base
      3 * (3 * (3 * (1 + (1 + (suc 0)))))
    ≡⟨⟩ -- suc 0 ≡ 1
      3 * (3 * (3 * (1 + (1 + 1))))
    ≡⟨⟩ -- + inductive
      3 * (3 * (3 * (1 + (suc (0 + 1)))))
    ≡⟨⟩ -- + base
      3 * (3 * (3 * (1 + (suc 1))))
    ≡⟨⟩ -- suc 1 ≡ 2
      3 * (3 * (3 * (1 + 2)))
    ≡⟨⟩ -- + inductive
      3 * (3 * (3 * (suc (0 + 2))))
    ≡⟨⟩ -- + base
      3 * (3 * (3 * (suc 2)))
    ≡⟨⟩ -- suc 2 ≡ 3
      3 * (3 * (3 * 3))
    ≡⟨⟩ -- continue until
      81
    ∎

  _∸_ : ℕ → ℕ → ℕ
  m     ∸ zero  = m
  zero  ∸ suc n = zero
  suc m ∸ suc n = m ∸ n

  _ =
    begin
      3 ∸ 2
    ≡⟨⟩
      2 ∸ 1
    ≡⟨⟩
      1 ∸ 0
    ≡⟨⟩
      1
    ∎
  
  _ =
    begin
      5 ∸ 3
    ≡⟨⟩
      4 ∸ 2
    ≡⟨⟩
      3 ∸ 1
    ≡⟨⟩
      2 ∸ 0
    ≡⟨⟩
      2
    ∎

  _ =
    begin
      3 ∸ 5
    ≡⟨⟩
      2 ∸ 4
    ≡⟨⟩
      1 ∸ 3
    ≡⟨⟩
      0 ∸ 2
    ≡⟨⟩
      0
    ∎
  
  infixl 6  _+_  _∸_
  infixl 7  _*_

  {-
    Recursive definition
    0       + n  ≡  n
    (suc m) + n  ≡  suc (m + n)

    Reducing our definition to equivalent inference rules for judgments about equality
    Inductive reasoning instead of recursive (bottom up instead of top down)
    n : ℕ
    --------------
    zero + n  =  n

    m + n  =  p
    ---------------------
    (suc m) + n  =  suc p

    -- In the beginning, we know nothing about addition.
    -- On the first day, we know about addition of 0.
    0 + 0 = 0     0 + 1 = 1    0 + 2 = 2     ...
    -- On the second day, we know about addition of 0 and 1.
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
    -- On the third day, we know about addition of 0, 1, and 2.
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
    2 + 0 = 2     2 + 1 = 3     2 + 2 = 4     2 + 3 = 5     ...
    -- etc

    https://math.stackexchange.com/questions/228863/recursive-vs-inductive-definition
    My best description is that "inductive definition" is more common when we are defining a set of objects "out of nothing", while "recursive definition" is more common when we are defining a function on an already-existing collection of objects.
  -}

  {- 
    First, we create the infinite set of naturals. We take that set as given when creating instances of addition, so even on day one we have an infinite set of instances.
    Instead, we could choose to create both the naturals and the instances of addition at the same time. Then on any day there would be only a finite set of instances:

    -- In the beginning, we know nothing.
    -- On the first day, we know zero.
    0 : ℕ
    -- On the second day, we know one and all sums that yield zero.
    0 : ℕ
    1 : ℕ    0 + 0 = 0
    -- On the third day, we know two and all sums that yield one.
    0 : ℕ
    1 : ℕ    0 + 0 = 0
    2 : ℕ    0 + 1 = 1   1 + 0 = 1
    -- On the fourth day, we know three and all sums that yield two.
    0 : ℕ
    1 : ℕ    0 + 0 = 0
    2 : ℕ    0 + 1 = 1   1 + 0 = 1
    3 : ℕ    0 + 2 = 2   1 + 1 = 2    2 + 0 = 2

    On the n’th day there will be n distinct natural numbers, and n × (n-1) / 2 equations about addition.
    The number n and all equations for addition of numbers less than n first appear by day n+1.
    This gives an entirely finitist view of infinite sets of data and equations relating the data.

    --------
    zero : ℕ

    m : ℕ
    ---------
    suc m : ℕ

    n : ℕ
    --------------
    zero + n  =  n

    m + n  =  p
    ---------------------
    (suc m) + n  =  suc p
  -}

  {-# BUILTIN NATPLUS _+_ #-}
  {-# BUILTIN NATTIMES _*_ #-}
  {-# BUILTIN NATMINUS _∸_ #-}

  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin
  
  inc : Bin → Bin
  inc ⟨⟩ = ⟨⟩ I
  inc (b O) = b I
  inc (b I) = (inc b) O

  _ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
  _ = refl

  to : ℕ → Bin
  to zero = ⟨⟩ O
  to (suc n) = inc (to n)

  from : Bin → ℕ
  from ⟨⟩ = 0
  from (b O) = from b * 2
  from (b I) = suc (from b * 2)

  _ : to 4 ≡ ⟨⟩ I O O
  _ = refl

  _ : from (⟨⟩ I O O) ≡ 4
  _ = refl

  -- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
