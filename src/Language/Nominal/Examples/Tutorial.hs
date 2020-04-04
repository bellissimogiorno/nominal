{-|
Module      : Tutorial 
Description : Name-binding for dummies: tutorial on use of nominal package 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

The interaction of name-binding with data can be tricky.  Examples include:

* Inductively defining syntax and reductions of a syntax with binding, e.g. lambda-calculus.
* Graph-like structures, especially if they have danging pointers.

This package implements a solution in Haskell, based on names and swappings.  With it, you can define data with name-binding and program on this data in a nice manner that closely mirrors informal practice.  There is no state monad of known names imposed, no global distinction between free names and bound names, capture-avoidance is taken care of very much in the background, and a well-studied mathematical reference model is available given by nominal techniques as referenced below. 

The maths is in <https://link.springer.com/article/10.1007/s001650200016 a new approach to abstract syntax with variable binding> (see also <http://www.gabbay.org.uk/papers.html#newaas-jv author's pdfs>).

This tutorial covers the main points of the package from the point of view of a working programmer wishing to see the functions being used.  It is best read directly from source code. 
One extended development is in "Language.Nominal.Examples.SystemF", with more in preparation.
-}

{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}


module Language.Nominal.Examples.Tutorial
--    ( 
--    )
    where

-- import Language.Nominal.Utilities 
import Language.Nominal.Names 
import Language.Nominal.Nom
import Language.Nominal.Abs 
import Language.Nominal.Sub 

-- * Basics of names

-- | Let's start by declaring a type of labels for names.  
-- Here, these labels are just strings.  
-- (More complex examples of labels are in the "SystemF" example, 
-- including labels that can themselves contain names.) 
type MyNameLabel = String 

-- | Declare a type of names labelled by our type for labels.  
-- An inhabitant of this type is a string-labelled name.  
-- Under the hood, names are implemented using "Unique", so they're just 
-- unique hashable atomic objects with a label attached. 
type MyName = Name MyNameLabel 

-- | Create a fresh name 'a'', which is wrapped in a 'myNameLabel'-name-binding context
a' :: Nom MyNameLabel MyName
a' = freshName "a" 

-- | Is @a' == a'@?  No!  
-- This is because evaluation is lazy, so two copies of 'a'' are created in two distinct local name-binding contexts; 
-- one to the left of the '==' and the other to the right.
step1 :: Bool
step1 = a' == a' 

-- * The monad of name-binding 

-- | 'Nom' is a monad.  Monad composition is capture-avoiding.
-- This is why the equality above returns 'False'.  
-- However, we can unpack 'a'' as @a : Name MyNameLabel@, using 'unsafeUnNom',
-- exposing it as a name.  
-- In a program we might also do this safely using '>>=' ... or maybe not.  
-- Removing a name-binding context just chooses concrete names for the binding.  
a :: MyName
a = unsafeUnNom a' 

-- | We're out of the monad.  'a' is 'a'.  Is @a == a@?  Yes!  
step2 :: Bool
step2 = a == a 

-- * Name-abstraction 

-- | Now abstract 'a' in 'a'.  Mathematically this would be written a.a.
-- Think of the a.a in λa.a.
absaa :: Abs MyNameLabel MyName
absaa = absByName a a 

-- | The abstraction is equal to itself.
step4 :: Bool
step4 = absaa == absaa 

-- | We can create a fresh name 'b' and concrete @a.a@ at 'a' to get 'a', or at 'b' to get 'b'.
-- WARNING: behaviour if we concrete an abstraction at a name that is not fresh, is undefined. 
b :: MyName
b = unsafeUnNom $ freshName "b"
step4a :: Bool
step4a = (conc absaa a) == a
step4b :: Bool
step4b = (conc absaa b) == b
step4warning :: (MyName, MyName)
step4warning = conc (absByName a (a,b)) b

-- * Nameless types

-- | Some types, like 'Bool' and 'String', are 'Nameless' and cannot contain names.  
-- The 'Nom' context can always be removed, using 'unNom'. 
-- Let's use that to recover the @a@ label.
-- The type is @Maybe MyNameLabel@ instead of @MyNameLabel@ because, for internal
-- reasons when creating atoms, it's useful to always have a default ('Nothing') label.
-- (We could also do this with a typeclass constraint, but typeclass constraints
--  create complications elsewhere.) 
step5 :: Maybe MyNameLabel 
step5 = unNom $ nameLabel <$> a'
-- | Having freed 'a' from its name-binding context, we can wrap it up again.
step6 :: Nom MyNameLabel MyName
step6 = res [a] a 
-- | This isn't equal to 'a'', as noted in 'step1'.
step7 :: Bool
step7 = a' == step6 

-- * Local scope out of global names 

-- | Now for a more involved example.  We check that restriction creates local scope.  
-- Should return 'True' on 'a'.
prop_split_scope :: MyName -> Bool
prop_split_scope n = unNom $ do -- Nom monad
   let (x1,x2) = (res [n] n, res [n] n) -- create two local scopes using the one name @n@
   y1 <- x1                             -- unpack the two scopes separately
   y2 <- x2                             -- two scopes, two distinct fresh names unpacked into @y1@ and @y2@
   return $ y1 /= y2                    -- check for equality (should return false)
step8 :: Bool
step8 = prop_split_scope a

-- * Swapping


-- | Let's give ourselves another name 
c :: MyName
c = unsafeUnNom $ freshName "c"

-- | We can swap 'a' and 'b', in simple types like lists ...
step9 :: [MyName]
step9 = swp a b [a,b,c,a,a,c] -- should return @[b,a,c,b,b,c]@

-- | ... and in not-so-simple types, like function-types. 
-- The typeclass of all swappable types is called 'Swappable'. 
step10 :: MyName -> MyName
step10 n 
   | n == a    = b
   | n == b    = c
   | n == c    = a
   | otherwise = n
-- | should return @[b,c,a]@
step10abc :: [MyName]
step10abc = map step10 [a, b, c] 
-- | 'swp' applied to the function
step10swp :: MyName -> MyName
step10swp = swp a b step10
-- | Apply it to @[a,b,c]@.  Should return @[c,a,b]@
step10swpabc :: [MyName] 
step10swpabc = map step10swp [a, b, c] -- should return @[c,a,b]@
-- | Should return 'True'. 
step11 :: Bool 
step11 = step10swpabc == [c, a, b]
-- | WARNING: 'swp' swaps the underlying atoms, but leaves labels alone.
-- If labels are used as display names (as above) then this may confuse.
-- This is a design tradeoff: are labels display names? 
-- (in which case our design decision is confusing)
-- or type information?
-- (in which case arguably it's right).
-- Watch the subscripts; they are the underlying identifiers. 
step12 :: [Maybe MyNameLabel]
step12 = map nameLabel step10swpabc

-- * Substitution

-- | We have a theory of substitution.
-- This works automatically on simple datatypes (like lists and name-abstractions) and can be
-- extended using typeclasses to more complex datatypes (see "SystemF").
step13 :: [MyName]
step13 = sub a b [a,b,c] -- should return [b,b,c]
-- | Should return @b'.[b,b',c]@ and it does.  Look at the subscripts (not the labels).
step14 :: Abs MyNameLabel [MyName]
step14 = sub a b $ absByName b [a,b,c]
-- | A larger development is in "SystemF".  Suggestions and comments welcome.

-- * Interaction of abstraction and functions

-- | @a.a@, @b.b@, @a.c@, and @b.c@ are all distinct.
-- But this is only because the abstraction stores the name labels 
-- ("a", "b", "a", and "b" respectively) of the bound name. 
step15a :: (Bool, Bool)
step15a = (absByName a a == absByName b b, absByName a c == absByName b c)

-- | Let's wipe those labels, and what we do next will be easier
an :: MyName
an = nameOverwriteLabel Nothing a
bn :: MyName
bn = nameOverwriteLabel Nothing b
cn :: MyName
cn = nameOverwriteLabel Nothing c

-- | Now note that @a.a == b.b@ and @a.c = b.c@ (up to name labels, which are now reset)
step15 :: (Bool, Bool)
step15 = (absByName an an == absByName bn bn, absByName an cn == absByName bn cn)
-- | Abstraction is capturing: @(\x -> a.x) a@ should evaluate to @a.a@
step16 :: Bool
step16 = ((\x -> absByName an x) an) == absByName an an 
-- | Thus @\x -> a.x@ and @\x -> b.x@ are not equal (the latter evalutes to @b.a@ on @a@).
step17 :: Bool
step17 = (\x -> absByName an x) an == (\x -> absByName bn x) an
-- | We can abstract in functions.
-- Consider a program involving @a.(\x -> a.x)@.  
-- The @a@ is abstracted ... in the abstraction function @\x -> a.x@.
-- So @a.(\x -> a.x)@ concreted at 'b' is @(\x -> b.x)@.
step18 :: Bool
step18 = ( (conc (absByName an (\x -> absByName an x)) an) an 
         , (conc (absByName an (\x -> absByName an x)) bn) an 
         ) == (absByName an an, absByName bn an)          

theEnd :: Bool
theEnd = True
 
