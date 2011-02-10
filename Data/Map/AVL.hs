{-# LANGUAGE GADTs, CPP, MagicHash, Rank2Types, ScopedTypeVariables, NamedFieldPuns #-}
module Data.Map.AVL (AVLMap, insertWithKey, lookup, mapWithKey, foldrWithKey, foldlWithKey, traverseWithKey) where

import Control.Applicative
import Data.Foldable
import Data.Traversable
import Data.Map.AVL.Internals
import Prelude hiding (lookup)

#define NIL (SNode _ Nil)
#define L(args) (SNode _ (LeftBin args))
#define B(args) (SNode _ (Balanced args))
#define R(args) (SNode _ (RightBin args))

data AVLMap k a where
  AVLMap :: !(SNode d k a) -> AVLMap k a

instance Functor (AVLMap k) where
  fmap f = mapWithKey (const f)

instance Foldable (AVLMap k) where
  foldr f z m = foldrWithKey (\ _ a z -> f a z) z m
  foldl f z m = foldlWithKey (\ z _ a -> f z a) z m

instance Traversable (AVLMap k) where
  traverse f m = traverseWithKey (const f) m

insertWithKey :: forall k a . Ord k => (k -> a -> a -> a) -> k -> a -> AVLMap k a -> AVLMap k a
insertWithKey f k a (AVLMap t) = runRes (ins t) AVLMap AVLMap where
  ins :: forall d . SNode d k a -> Res d k a
  ins NIL = res' $ singleton k a
  ins R(kx x l r) = case compare k kx of
    LT	-> joinL kx x (ins l) r
    EQ	-> res (bin kx (f kx a x) l r)
    GT	-> joinR kx x l (ins r)
  ins B(kx x l r) = case compare k kx of
    LT	-> joinL kx x (ins l) r
    EQ	-> res (bin kx (f kx a x) l r)
    GT	-> joinR kx x l (ins r)
  ins L(kx x l r) = case compare k kx of
    LT	-> joinL kx x (ins l) r
    EQ	-> res (bin kx (f kx a x) l r)
    GT	-> joinR kx x l (ins r)

insertMin, insertMax :: k -> a -> SNode d k a -> Res d k a
insertMin k a NIL		= res' $ singleton k a
insertMin k a L(kx x l r)	= joinL kx x (insertMin k a l) r
insertMin k a B(kx x NIL ~NIL)	= res' (bin kx x (singleton k a) nil)
insertMin k a B(kx x l r)	= joinL kx x (insertMin k a l) r
insertMin k a R(kx x NIL r)	= res (bin kx x (singleton k a) r)
insertMin k a R(kx x l r)	= joinL kx x (insertMin k a l) r

insertMax k a NIL		= res'  $ singleton k a
insertMax k a L(kx x l NIL)	= res (bin kx x l (singleton k a))
insertMax k a L(kx x l r)	= joinR kx x l (insertMax k a r)
insertMax k a B(kx x ~NIL NIL)	= res' (bin kx x nil (singleton k a))
insertMax k a B(kx x l r)	= joinR kx x l (insertMax k a r)
insertMax k a R(kx x l r)	= joinR kx x l (insertMax k a r)

#define GLUE if sz l >= sz r then let !(k, a, l') = deleteFindMax l in joinL k a l' r else \
	let !(k, a, r') = deleteFindMin r in joinR k a l r'

glue :: SNode d k a -> SNode d k a -> Res d k a
glue l r | l `seq` r `seq` False	= undefined
glue NIL _		= res nil
glue l@L(_ _ _ _) r	= GLUE
glue l@B(_ _ _ _) r	= GLUE
glue l@R(_ _ _ _) r	= GLUE

lookup :: Ord k => k -> SNode d k a -> Maybe a
lookup _ NIL	= Nothing
lookup k L(kx x l r)	= case compare k kx of
  LT	-> lookup k l
  EQ	-> Just x
  GT	-> lookup k r
lookup k B(kx x l r)	= case compare k kx of
  LT	-> lookup k l
  EQ	-> Just x
  GT	-> lookup k r
lookup k R(kx x l r)	= case compare k kx of
  LT	-> lookup k l
  EQ	-> Just x
  GT	-> lookup k r

mapWithKey :: forall k a b . (k -> a -> b) -> AVLMap k a -> AVLMap k b
mapWithKey f (AVLMap t) = AVLMap (smap t) where
  nmap :: forall d . Node d k a -> Node d k b
  nmap Nil = Nil
  nmap (LeftBin kx x l r) = LeftBin kx (f kx x) (smap l) (smap r)
  nmap (Balanced kx x l r) = Balanced kx (f kx x) (smap l) (smap r)
  nmap (RightBin kx x l r) = RightBin kx (f kx x) (smap l) (smap r)
  {-# INLINE smap #-}
  smap :: forall d . SNode d k a -> SNode d k b
  smap SNode{sz, node} = SNode{sz, node = nmap node}

foldrWithKey :: forall k a b . (k -> a -> b -> b) -> b -> AVLMap k a -> b
foldrWithKey f z (AVLMap t) = fold t z where
  fold :: forall d . SNode d k a -> b -> b
  fold NIL z = z
  fold L(kx x l r) z = fold l $ f kx x $ fold r z
  fold B(kx x l r) z = fold l $ f kx x $ fold r z
  fold R(kx x l r) z = fold l $ f kx x $ fold r z

foldlWithKey :: forall k a b . (b -> k -> a -> b) -> b -> AVLMap k a -> b
foldlWithKey f z (AVLMap t) = fold z t where
  fold :: forall d . b -> SNode d k a -> b
  fold z NIL = z
  fold z L(kx x l r) = f (z `fold` l) kx x `fold` r
  fold z B(kx x l r) = f (z `fold` l) kx x `fold` r
  fold z R(kx x l r) = f (z `fold` l) kx x `fold` r

traverseWithKey :: forall f k a b . Applicative f => (k -> a -> f b) -> AVLMap k a -> f (AVLMap k b)
traverseWithKey f (AVLMap (SNode sz t)) = AVLMap . SNode sz <$> trav t where
  trav :: forall d . Node d k a -> f (Node d k b)
  trav Nil = pure Nil
  trav (LeftBin kx x (SNode szl l) (SNode szr r)) =
    result <$> f kx x <*> trav l <*> trav r
    where result x' l' r' = LeftBin kx x' (SNode szl l') (SNode szr r')
  trav (Balanced kx x (SNode szl l) (SNode szr r)) =
    result <$> f kx x <*> trav l <*> trav r
    where result x' l' r' = Balanced kx x' (SNode szl l') (SNode szr r')
  trav (RightBin kx x (SNode szl l) (SNode szr r)) =
    result <$> f kx x <*> trav l <*> trav r
    where result x' l' r' = RightBin kx x' (SNode szl l') (SNode szr r')