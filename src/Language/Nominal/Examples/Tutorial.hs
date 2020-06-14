{-|
Module      : Tutorial 
Description : Name-binding for dummies: tutorial on use of nominal package 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

= Name-binding for dummies: tutorial on use of nominal package  

-}

{-# LANGUAGE CPP                   
           , FlexibleInstances     
           , InstanceSigs          
           , LambdaCase            
           , MultiParamTypeClasses 
#-}

{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports   #-}

module Language.Nominal.Examples.Tutorial
    ( 
      -- $blurb

      -- * Basics of names
      -- $basics
      MyNameLabel
    , MyName  
      -- * Creating fresh names
      -- $setup
      
      -- * Creating @'Nom'@ bindings with @'res'@ 
      -- $res

      -- * Binding multiple names
      -- $multiple

      -- * Local scope out of global names 
      -- $local

      -- * Nameless types
      -- $nameless

      -- * The monad of name-binding 
      -- $bindings
      
      

      -- * Name-abstraction 
      -- $abstraction

      -- * Functorial action of binders
      -- $abs_functorial

      -- * Swapping
      -- $swapping
 
      -- * Unification up to permutation 
      -- $unify

      -- * Substitution
      -- $substitution

      -- * Names and atoms
      -- $atoms
    )
    where

import Data.Default

import Language.Nominal.Name 
import Language.Nominal.Nom
import Language.Nominal.Binder
import Language.Nominal.Abs 
import Language.Nominal.Sub 
import Language.Nominal.Unify

#include "../Blurb.txt"

{- $basics

Let's start by declaring a type @'MyNameLabel'@ of labels for names; our labels are just strings.  

__Example:__ More complex examples of labels are in the "Language.Nominal.Examples.SystemF" example, including labels that can themselves contain names.
 
Then we create a type @'MyName'@ of @'MyNameLabel'@-labelled names. 
An inhabitant of this type is a string-labelled name.  
Under the hood names are implemented a pair of a "Unique" identifier, and a label.  
So names are just unique hashable atomic objects with a label attached. 


-}

type MyNameLabel = String 
type MyName = Name MyNameLabel 


{-- a' :: Nom MyName
a' = freshName "a"

a, b :: MyName
a = genUnNom a'
b = genUnNom $ freshName "b"



__Warning:__ Watch the subscripts; they are the underlying identifiers.
-- They do match up with the display names in this case, but they don't have to in general.
step12 :: [MyNameLabel]
step12 = map nameLabel step10swpabc

-- The typeclass of all swappable types is called 'Swappable'. 
-- | Swapping applied to the function
step10swpN :: MyName -> MyName
-- | Apply it to @[a,b,c]@.  Should return @[c,a,b]@
step10swpabc :: [MyName] 
step10swpabc = map step10swpN [a, b, c] -- should return @[c,a,b]@
-- | Should return 'True'. 
step11 :: Bool 
step11 = step10swpabc == [c, a, b]
-- | WARNING: Watch the subscripts; they are the underlying identifiers.
-- They do match up with the display names in this case, but they don't have to in general.
step12 :: [MyNameLabel]
step12 = map nameLabel step10swpabc

-- * Interaction of abstraction and functions

-- | @a.a@, @b.b@, @a.c@, and @b.c@ are all distinct.
-- But this is only because the abstraction stores the name labels 
-- ("a", "b", "a", and "b" respectively) of the bound name. 
step15a :: (Bool, Bool)
step15a = (abst a a == abst b b, abst a c == abst b c)

-- | Let's wipe those labels to a default value, and what we do next will be easier
an :: MyName
an = nameOverwriteLabel def a
bn :: MyName
bn = nameOverwriteLabel def b
cn :: MyName
cn = nameOverwriteLabel def c

-- | Now note that @a.a == b.b@ and @a.c = b.c@ (up to name labels, which are now reset)
step15 :: (Bool, Bool)
step15 = (abst an an == abst bn bn, abst an cn == abst bn cn)
-- | Abstraction is capturing: @(\x -> a.x) a@ should evaluate to @a.a@ 
-- (hlint complains about this and the examples which follow, because 
-- the left-hand side is just an eta-conversion.  However,
--  that's the point: names are bound as if name-binding was just a pair of a name and a datum.) 
step16 :: Bool
step16 = (\x -> abst an x) an == abst an an 
-- | Thus @\x -> a.x@ and @\x -> b.x@ are not equal (the latter evalutes to @b.a@ on @a@).
step17 :: Bool
step17 = (\x -> abst an x) an == (\x -> abst bn x) an
-- | We can abstract in functions.
-- Consider a program involving @a.(\x -> a.x)@.  
-- The @a@ is abstracted ... in the abstraction function @\x -> a.x@.
-- So @a.(\x -> a.x)@ concreted at 'b' is @(\x -> b.x)@.
step18 :: Bool
step18 = ( (conc (abst an (\x -> abst an x)) an) an 
         , (conc (abst an (\x -> abst an x)) bn) an 
         ) == (abst an an, abst bn an)          

theEnd :: Bool
theEnd = True
--}
 
{- $setup

  
   Let's create a fresh name @a'@.  Note that it's wrapped in a name-binding monad @'Nom'@; more on that shortly.
  
   >>> let a' = freshName "a" :: Nom MyName
  
   Is @a' == a'@?
   
   >>> a' == a'
   False
  
   No!
   This is because evaluation is lazy, so two copies of @a'@ are created in two distinct local name-binding contexts; 
   one to the left of the @'=='@ and the other to the right.
   
   But we can unpack that context using @'genUnNom'@.  This triggers the computation of actual fresh identifiers for any bindings:
  
   >>> let a = genUnNom a' :: MyName

   Is @a == a@?
   
   >>> a == a
   True

   Yes!  @a@ is just a plain datum, whose name-identifier was generated fresh a moment ago when we invoked @'genUnNom'@.  So if we do this again:

   >>> let b = genUnNom a' :: MyName
   >>> a == b
   False

   This is to be expected: the unique identifier of @b@ was generated fresh for that of @a@. 
   
   __Warning__: The label of @b@ is still @"a"@ ... of course:

   >>> nameLabel b
   "a"
   >>> nameLabel a == nameLabel b
   True
-}

{- $res
   Having freed @a@ from its name-binding context, we can wrap it up again.
  
   >>> let a'' = resN [a] a :: Nom MyName
  
   This isn't equal to @a'@ because the name bound in @a''@ is bound by a separate context from that bound in @a'@: 
  
   >>> a' == a''
   False
-}

{- $multiple
 
   We can bind multiple names simultaneously:
   
   >>> let x1 = resN [a,b] (a,a,b) :: Nom (MyName, MyName, MyName)

   We'll see more of @x1@ later.

-}

{- $local

   Now for a more involved example.  We show how @'resN'@ creates local scope:

   >>> :set -XScopedTypeVariables
   >>> let prop_split_scope (n :: MyName) = (resN [n] n) /= (resN [n] n)

   Note we use /one/ input name @n@ to create /two/ output local scopes.  This should return @'True'@ on @a@:

   >>> prop_split_scope a
   True
-}

{- $nameless
   Some types, like @'Bool'@ and @'String'@, are @'Nameless'@.  
   E.g. if we have a truth-value, we know it doesn't have any names in it; we might have used names to calculate the truth-value, but the truth-value itself @'True'@ or @'False'@ is nameless.
 
   On @'Nameless'@ types the @'Nom'@ context can always be removed.  We can use @'unNom'@ (a general and versatile function which happens to be useful in this instance). 
   Let's illustrate this by safely extracting @a@'s nameless 'String' label: 
  
   >>> unNom $ nameLabel <$> a' :: MyNameLabel
   "a"
-} 

{- $bindings
   @'Nom'@ is a monad.  We can use monad composition @'>>='@ to go under a binder: 
  
   >>> unNom $ a' >>= \a -> return $ a == a
   True
 
   We can use monad composition to merge binding contexts in a capture-avoiding manner.  Compare @x1@ with @x2@ below:

   >>> let x1 = resN [a,b] (a,a,b) :: Nom (MyName, MyName, MyName)
   >>> let x2 = a' >>= \a -> a' >>= \b -> return (a,a,b) :: Nom (MyName, MyName, MyName) 
   
   @x2@ is /morally equal/ to @x1@, though an equality test will return @False@ because they each have their own local binding context.  

   >>> x1 == x2
   False

   @x1@ and @x2@ are /unifiable/.  We'll come to that later.

-}

{- $abstraction

   The package offers facilities for @'Abs'@traction.  Let's @'abst'@ract @a@ in @a@: 
  
   >>> absaa = abst a a :: Abs MyNameLabel MyName
  
   Think of @absaa@ as the @a.a@ in @λa.a@.
   Unlike the @'res'@ binding @'x1'@, this abstraction is equal to itself ...
  
   >>> absaa == absaa
   True
   
   ... and to any other alpha-equivalent abstraction:

   >>> absaa == abst b b
   True
   
   Likewise:
   
   >>> let c = (genUnNom $ freshName "a") :: MyName
   >>> abst b [a, b]  ==  abst c [a, c] 
   True

   __Warning:__ The label of the abstracted name is preserved; only its identifier gets alpha-converted.  Thus, this returns false, just because @"a" /= "d"@:
   
   >>> let d = (genUnNom $ freshName "d") :: MyName
   >>> abst b [a, b]  ==  abst d [a, d] 
   False 

   We can concrete @absaa@ at @a@ to get @a@, or at @b@ to get @b@.
  
   >>> conc absaa a == a
   True
  
   >>> conc absaa b == b
   True

   Name labels come from the abstraction, whereas the name's identifier comes from the argument. 
   Thus, we get @"a"@ below and not @"d"@ (recall the labels of @a@, @b@, and @c@ are @"a"@ and the label of @d@ is @"d"@):

   >>> nameLabel a
   "a"
   >>> nameLabel d
   "d"
   >>> nameLabel (conc absaa d) 
   "a"

   __Example:__ There are many examples of using abstractions in "Language.Nominal.Examples.SystemF".  
 
   __Warning__: Behaviour if we concrete an abstraction at a name that is not fresh, is undefined. 

   >>> conc (abst a (a, b)) b :: (MyName, MyName)
   ...

-}

{- $abs_functorial

   Our machinery now pays dividends.  Abstraction is functorial, and capture-avoidance is automagical: 
 
   >>> let aTob = (map $ \n -> if n == a then b else n) :: [MyName] -> [MyName]
   >>> let c = (genUnNom $ freshName "a") :: MyName
   >>> (aTob <$> abst a [a, b])  ==  abst a [a, b] 
   True
   >>> (aTob <$> abst b [a, b])  ==  abst c [b, c]  
   True

   Another equally valid rendering of the second example above, because alpha-equivalence allows it:

   >>> (aTob <$> abst b [a, b])  ==  abst a [b, a]  
   True
   
   __Note__: @'resN'@ is functorial in the same way, but it unbinds its local scope differently from @'abst'@:  
   
   >>> resN [a] a == resN [a] a
   False
   
   >>> abst a a == abst a a
   True
-}  

-- * Swapping
{- $swapping

>>> let [a, b, c] = genUnNom $ freshNames ["a", "b", "c"]

We can swap @a@ and @b@ in simple types like lists ...

>>> swpN a b [a,b,c,a,a,c] == [b,a,c,b,b,c]
True

... and in not-so-simple types, like 'Abs', 'Nom', and function-types. 

>>> :{ 
 f n  
   | n == a    = b
   | n == b    = c
   | n == c    = a
   | otherwise = n
:}

>>> map f [a, b, c] == [b, c, a]
True

>>> fswp = swpN a b f 
>>> map fswp [a, b, c] == [c, a, b]
True

-}


{- $unify
   Recall @x1@ and @x2@ above; let's reconstruct them here:

   >>> let [a, b] = genUnNom $ freshNames ["a", "b"] 
   >>> let x1 = resN [a,b] (a,a,b) :: Nom (MyName, MyName, MyName)
   >>> let x2 = x1                 :: Nom (MyName, MyName, MyName)
   
   We noted that @x1@ and @x2@ are not equal because they have distinct local scopes:
   
   >>> x1 == x2
   False

   However, they /are/ unifiable:
   
   >>> unifiablePerm x1 x2
   True

   If a type is sufficiently structured, 'unifiablePerm' can be used as an equality predicate that tries to unify local scopes.  More on this in "Language.Nominal.Unify", with many example applications in "Language.Nominal.Examples.IdealisedEUTxO".

-}

{- $substitution

We have a theory of substitution given by a typeclass @'Sub'@ with function @'sub'@.
This works automatically on simple datatypes (like lists and name-abstractions) and can be extended using typeclasses to more complex datatypes (see "Language.Nominal.Examples.SystemF").

>>> [a, b, b', c] = genUnNom $ freshNames [(), (), (), ()] 
>>> sub a b [a,b,c] == [b,b,c]
True
>>> (sub a b $ abst b [a,b,c]) == abst b' [b, b', c]
True

__Gotcha__: The expression below might not mean what you think.  Note the bracketing!

>>> sub a b $ abst b [a,b,c] == abst b' [b, b', c]
False

-}

{- $atoms

We actually have two species of identifier:

* Names (like @'Name' 'String'@) , as discussed above, and
* atoms (like @'Atom'@).

Both names and atoms are datatypes of bindable identifiers, but names come with labels and atoms don't.
An atom is essentially identical to a @()@-labelled name, and conversely a name is essentially identical to a pair of an atom and the name's label.

So why maintain both?  

* /If you need identifiers with no semantic information,/ then use atoms.  We do this in "Language.Nominal.Examples.IdealisedEUTxO", where atoms are used to identify locations in a blockchain.  
Because our identifiers have no semantic content aside from pointing to themselves, we use atoms.

* /If you need identifiers with associated semantic information/ (e.g. a denotation, a type, or even just a display name), then you might prefer to use names.  We do this in "Language.Nominal.Examples.SystemF", where term names 'Language.Nominal.Examples.SystemF.NTrm' are labelled with types 'Language.Nominal.Examples.SystemF.Typ'.

* Although we can emulate atoms as @()@-labelled names, these are not quite the same thing.  
Atoms are interesting because they give us swapping, and swapping gives us 'res' and 'abst'. 
Names (i.e. labelled atoms) are built /on top of/ this underlying structure.  (So even if we only exposed names and not atoms, the atoms would still be there.) 

Sometimes functions come in two versions: an atoms-version and a names-version (e.g. 'swp' and 'swpN', and 'res' and 'resN'). 
Where this occurs, the N (for 'Name') version just discards labels and calls the atoms-version.

/Instead of names, why not maintain a state lookup monad, associating atoms to their semantic information?/
We could, but we'd have to thread it through our computations (if they need labelled atoms), incurring overhead that defeats a purpose of the design of this package, to /not/ require everything to happen inside a 'Nom' monad (see for example @prop_split_scope@ above).
It is a principle of nominal techniques that /names are data/: pure data should not require an omnipresent top-level monad.

__Gotcha:__ Names are compared for equality on their atoms.  Labels are discarded during the equality check:

>>> a = genUnNom $ freshName "a" 
>>> b = a `withLabel` "b"
>>> a == b
True

Wait, we can explain!  

* We get 'Eq' and 'Ord' instances of name-types (because atoms have them) even if the labels don't. 

* We get "Data.Map" on name-types, again even if the labels lack 'Eq' or 'Ord'.
 
* Have you considered why you're asking for this?  A name is an atomic ID tagged with information, and one atom occurring associated to multiple tags is like one license plate number on multiple cars; that's /not/ what /unique/ identifiers are meant for.  Or if you must do this, you can, but then it's up to you to keep track of which label (or combination of labels) is "true".  This package makes it easy to create fresh atoms, so perhaps you'd be better off creating multiple fresh atoms and giving a distinct label to each one.


-}


 
