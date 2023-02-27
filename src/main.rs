#![allow(dead_code)]

use std::{marker::PhantomData, any::TypeId};

fn main() {

    // ```
    // let v = 3 + 4;
    // let foo = v;
    // return v;
    // ```
    let ast = fix::<BlockStmtF<TyParam>>(BlockStmt {
        span: Span,
        stmts: vec![
            fix(Stmt::Let(fix(LetStmt {
                span: Span,
                ident: String::from("v"),
                init: fix(Expr::Add(
                    Box::new(fix(Expr::NumLit(3))),
                    Box::new(fix(Expr::NumLit(4))),
                )),
            }))),
            fix(Stmt::Let(fix(LetStmt {
                span: Span,
                ident: String::from("foo"),
                init: fix(ExprF::Ident(String::from("v"))),
            }))),
            fix(Stmt::Return(fix(ReturnStmt {
                span: Span,
                expr: fix(Expr::Ident(String::from("v")))
            })))
        ],
    });
    let count = cata(&CountLetsCataFn, ast.clone()).count;
    println!("{count}");

    let ast2 = cata(&IdentityCataFn, ast).into_inner();
    println!("{ast2:#?}");
}

/* --- usage: count number of declared variables --- */

#[derive(Clone, Copy)]
struct CountLetsCataFn;

impl CataFn for CountLetsCataFn {
    type F = CountLets<TyParam>;

    fn call<N>(&self, n: SAstNode<N>, node: N::TyCons<Self::F>) -> CountLets<N>
    where
        N: AstFunctor + 'static,
    {
        match n {
            // Base case, found one let statement
            SAstNode::LetStmt(_) => CountLets::new(1),
            SAstNode::Stmt(proof) => match proof.transmute_hkt(node) {
                StmtF::Block(inner) => inner.cast(),
                StmtF::Expr(inner) => inner.cast(),
                StmtF::If(inner) => inner.cast(),
                StmtF::Let(inner) => inner.cast(),
                StmtF::Return(inner) => inner.cast(),
            },
            SAstNode::BlockStmt(proof) =>
                CountLets::new(
                    proof.transmute_hkt(node)
                        .stmts
                        .into_iter()
                        .map(|stmt| stmt.count)
                        .sum::<usize>()
                ),
            SAstNode::IfStmt(proof) => CountLets::new({
                let IfStmtF { cond, then_block, else_block, .. } = proof.transmute_hkt(node);
                cond.count + then_block.count + else_block.map(|c| c.count).unwrap_or(0)
            }),
            // We already know it's going to be 0
            SAstNode::ReturnStmt(_)
            | SAstNode::Expr(_) => CountLets::new(0),
        }
    }
}

struct CountLets<F: AstNode> {
    count: usize,
    _marker: PhantomData<fn(F) -> F>,
}

impl<F: AstNode> CountLets<F> {
    fn new(count: usize) -> Self {
        CountLets { count, _marker: PhantomData }
    }

    fn cast<U: AstFunctor>(self) -> CountLets<U> {
        CountLets::<U>::new(self.count)
    }
}

impl AstTy for CountLets<TyParam> {
    type TyCons<F: AstNode> = CountLets<F>;
}

impl<F: AstNode> Clone for CountLets<F> {
    fn clone(&self) -> Self {
        CountLets::new(self.count)
    }
}

/* --- usage: traverse the ast without changin anything --- */

// Won't change the AST, but will transform it's types into an equivalent AST.
#[derive(Clone, Copy)]
struct IdentityCataFn;

impl CataFn for IdentityCataFn {
    type F = Identity<TyParam>;

    fn call<N>(&self, n: SAstNode<N>, node: N::TyCons<Self::F>) -> Identity<N>
    where
        N: AstFunctor + 'static,
    {
        match n {
            SAstNode::Stmt(proof) => Identity::Stmt(proof, {
                match proof.transmute_hkt(node) {
                    StmtF::Block(inner) => Stmt2::Block(inner.into_inner()),
                    StmtF::Expr(inner) => Stmt2::Expr(inner.into_inner()),
                    StmtF::If(inner) => Stmt2::If(inner.into_inner()),
                    StmtF::Let(inner) => Stmt2::Let(inner.into_inner()),
                    StmtF::Return(inner) => Stmt2::Return(inner.into_inner()),
                }
            }),
            SAstNode::BlockStmt(proof) => Identity::BlockStmt(proof, {
                let block = proof.transmute_hkt(node);
                BlockStmt2 {
                    span: block.span,
                    stmts: block.stmts
                        .into_iter()
                        .map(|stmt| stmt.into_inner())
                        .collect(),
                }
            }),
            SAstNode::IfStmt(proof) => Identity::IfStmt(proof, {
                let if_stmt = proof.transmute_hkt(node);
                IfStmt2 {
                    span: if_stmt.span,
                    cond: if_stmt.cond.into_inner(),
                    then_block: if_stmt.then_block.into_inner(),
                    else_block: if_stmt.else_block.map(|block| block.into_inner())
                }
            }),
            SAstNode::LetStmt(proof) => Identity::LetStmt(proof, {
                let let_stmt = proof.transmute_hkt(node);
                LetStmt2 {
                    span: let_stmt.span,
                    ident: let_stmt.ident,
                    init: let_stmt.init.into_inner(),
                }
            }),
            SAstNode::ReturnStmt(proof) => Identity::ReturnStmt(proof, {
                let ret_stmt = proof.transmute_hkt(node);
                ReturnStmt2 {
                    span: ret_stmt.span,
                    expr: ret_stmt.expr.into_inner(),
                }
            }),
            SAstNode::Expr(proof) => Identity::Expr(proof, {
                match proof.transmute_hkt(node) {
                    ExprF::Ident(inner) => Expr2::Ident(inner),
                    ExprF::Add(lhs, rhs) => Expr2::Add(Box::new(lhs.into_inner()), Box::new(rhs.into_inner())),
                    ExprF::NumLit(lit) => Expr2::NumLit(lit),
                }
            }),
        }
    }
}

// We already know which variant it's going to be active based on `F`. One possible thing is to use
// a "raw" `union`, but that would only save a single byte or so of memory. And the size `Identity`
// will grow with the size of the largest variant. However, what we really want is some type that
// is just a `#[repr(transparent)]` wrapper around our ast2 type and uses `F` to know at compile
// time, which type it is storing. In order to try to implement this, the first thing that comes to
// mind is
//
// ```rust
// struct Identity<F: AstFunctor + AstToAst2>(<F as AstToAst2>::Equiv);
//
// trait AstToAst2 {
//     type Equiv;
// }
//
// impl AstToAst2 for Stmt<TyParam> {
//     type Equiv = Stmt2;
// }
// /*...*/
// ```
//
// and then we just implement `AstToAst2` for every type that implements `AstFunctor`. However,
// that, in the `CataFn::call` method, the return type will be `Identity<N>` where `N: AstFunctor`.
// and not `N: AstFunctor + AstToAst2`. What we might thing of doing then is this
//
// ```rust
// // No extra bound on `F`.
// struct Identity<F: AstFunctor>(<F as AstToAst2>::Equiv);
//
// trait AstToAst2 {
//     type Equiv;
// }
//
// impl<T: AstFunctor> AstToAst2 for T {
//     type Equiv = ???;
// }
// ```
//
// we need to have different values for `Equiv` for diferent values of `T` which we can't do here.
// Using nightly we can get pretty close, but not quite
//
// ```rust
// trait AstToAst2 {
//     type Equiv;
// }
//
// // Base case is never actually used. Works to ensure that `AstToAst2` is indeed implemented for
// // every type that implements `AstFunctor`.
// impl<T: AstFunctor> AstToAst2 for T {
//     default type Equiv = !;
// }
//
// impl AstToAst2 for Stmt<TyParam> {
//     type Equiv = Stmt2;
// }
// /*...*/
// ```
//
// the problem now is that the return type of `CataFn::call` is `Identity<N>` which the compiler
// doesn't yet know which `N` it is, so it falls back to the default, `!`. So the function is
// expecting to return `Identity<N>` but what you can actually produce is something like
// `Identity<Stmt<TyParam>>` which are incompatible because their `AstToAst2::Equiv` types are not
// the same. Trying to force this to compile will cause UB since the caller of the function would
// allocate space for `!` (probably 0 bytes), but the function will try to return something that
// has an AST2 node in it.
//
enum Identity<F: AstNode> {
    Stmt(TEq<F, StmtF<TyParam>>, Stmt2),
    BlockStmt(TEq<F, BlockStmtF<TyParam>>, BlockStmt2),
    IfStmt(TEq<F, IfStmtF<TyParam>>, IfStmt2),
    LetStmt(TEq<F, LetStmtF<TyParam>>, LetStmt2),
    ReturnStmt(TEq<F, ReturnStmtF<TyParam>>, ReturnStmt2),
    Expr(TEq<F, ExprF<TyParam>>, Expr2),
}

impl Identity<StmtF<TyParam>> {
    fn into_inner(self) -> Stmt2 {
        // Having `self` with `F = Stmt<TyParam>` is proof that it is `Identity::Stmt`, since the
        // only way to construct a `Identity<Stmt<TyParam>>` is with that variant.
        let Identity::Stmt(_, inner) = self else { unreachable!() };
        inner
    }
}

impl Identity<BlockStmtF<TyParam>> {
    fn into_inner(self) -> BlockStmt2 {
        let Identity::BlockStmt(_, inner) = self else { unreachable!() };
        inner
    }
}

impl Identity<IfStmtF<TyParam>> {
    fn into_inner(self) -> IfStmt2 {
        let Identity::IfStmt(_, inner) = self else { unreachable!() };
        inner
    }
}

impl Identity<LetStmtF<TyParam>> {
    fn into_inner(self) -> LetStmt2 {
        let Identity::LetStmt(_, inner) = self else { unreachable!() };
        inner
    }
}

impl Identity<ReturnStmtF<TyParam>> {
    fn into_inner(self) -> ReturnStmt2 {
        let Identity::ReturnStmt(_, inner) = self else { unreachable!() };
        inner
    }
}

impl Identity<ExprF<TyParam>> {
    fn into_inner(self) -> Expr2 {
        let Identity::Expr(_, inner) = self else { unreachable!() };
        inner
    }
}

impl AstTy for Identity<TyParam> {
    type TyCons<F: AstNode> = Identity<F>;
}

impl<F: AstNode> Clone for Identity<F> {
    fn clone(&self) -> Self {
        use Identity::*;

        match self {
            Stmt(proof, inner) => Stmt(*proof, inner.clone()),
            BlockStmt(proof, inner) => BlockStmt(*proof, inner.clone()),
            IfStmt(proof, inner) => IfStmt(*proof, inner.clone()),
            LetStmt(proof, inner) => LetStmt(*proof, inner.clone()),
            ReturnStmt(proof, inner) => ReturnStmt(*proof, inner.clone()),
            Expr(proof, inner) => Expr(*proof, inner.clone()),
        }
    }
}

#[derive(Debug, Clone)]
enum Stmt2 {
    Block(BlockStmt2),
    Expr(Expr2),
    If(IfStmt2),
    Let(LetStmt2),
    Return(ReturnStmt2),
    /*...*/
}

#[derive(Debug, Clone)]
struct BlockStmt2 {
    span: Span,
    stmts: Vec<Stmt2>,
}

#[derive(Debug, Clone)]
struct IfStmt2 {
    span: Span,
    cond: Expr2,
    then_block: BlockStmt2,
    else_block: Option<BlockStmt2>,
}

#[derive(Debug, Clone)]
struct LetStmt2 {
    span: Span,
    ident: Ident,
    init: Expr2,
}

#[derive(Debug, Clone)]
struct ReturnStmt2 {
    span: Span,
    expr: Expr2,
}

#[derive(Debug, Clone)]
enum Expr2 {
    Ident(Ident),
    Add(Box<Expr2>, Box<Expr2>),
    NumLit(i64),
}

/* --- schemes --- */

// Ideally this would be a function argument to `cata`, but it can't
// since it needs to be generic over `N`.
trait CataFn {
    type F: AstTy;
    fn call<N>(
        &self,
        n: SAstNode<N>,
        node: N::TyCons<Self::F>
    ) -> <Self::F as AstTy>::TyCons<N>
    where
        N: AstFunctor + 'static;
}

impl<'a, T: CataFn + 'a> CataFn for &'a T {
    type F = T::F;
    fn call<N>(
        &self,
        n: SAstNode<N>,
        node: N::TyCons<Self::F>
    ) -> <Self::F as AstTy>::TyCons<N>
    where
        N: AstFunctor + 'static,
    {
        (*self).call(n, node)
    }
}

fn cata<'a, N, C>(f: &'a C, node: Fix<N>) -> App<C::F, N>
where
    N: AstFunctor + 'static,
    C: CataFn + 'a,
{
    struct Fn<'a, C: CataFn>(&'a C);

    impl<'a, C> AstNodeMapFn<Fix<TyParam>, C::F> for Fn<'a, C>
    where
        C: CataFn + 'a,
    {
        fn call<N>(&self, x: Fix<N>) -> App<C::F, N>
        where
            N: AstFunctor + 'static,
        {
            cata::<'a, N, C>(self.0, x)
        }
    }
    f.call(SAstNode::<N>::new(), N::fmap(Fn(f), node.out()))
}

/* --- traits --- */

// Represents the fact that `Self` has kind `AstFunctor -> Type`
trait AstTy {
    type TyCons<N: AstNode>: Clone /* unfortunatelly appears to be needed */;
}

// The family of types used in the AST. It has kind `(AstNode -> Type) -> Type`.
trait AstNode {
    // The type constructor for `Self`.
    type TyCons<F: AstTy>: Clone;
}

// Functors (I think) that map nodes in the `AstNode` family.
// `type AstFunctor :: ((AstNode -> Type) -> Type) -> Constaint
trait AstFunctor: AstNode {
    // `fmap :: (forall n. u n -> g n) -> f u -> f g`
    fn fmap<F, U, G>(f: F, x: Self::TyCons<U>) -> Self::TyCons<G>
    where
        F: AstNodeMapFn<U, G>,
        U: AstTy,
        G: AstTy;
}

// Represents a generic function. It needs to be a trait because rust won't allow generic function
// parameters directly.
trait AstNodeMapFn<U, G>
where
    U: AstTy,
    G: AstTy,
{
    fn call<N>(&self, x: App<U, N>) -> App<G, N>
    where
        N: AstFunctor + 'static;
}

/* --- support types --- */

// Isomorphic to the never type, it is ment to be used by higher kinded
// types in type impl. `MyType<TyParam>` is the same as `MyType`
// alone, representing `MyType` has kind `Type -> Type`
#[derive(Clone, Copy)]
enum TyParam {}

impl AstNode for TyParam {
    type TyCons<F: AstTy> = TyParam;
}

impl AstFunctor for TyParam {
    fn fmap<F, U, G>(_: F, x: TyParam) -> Self::TyCons<G>
    where
        F: AstNodeMapFn<U, G>,
        U: AstTy,
        G: AstTy,
    {
        // We can never get here because it is impossible to construct `x`.
        match x { }
    }
}

impl AstTy for TyParam {
    type TyCons<N: AstNode> = TyParam;
}

type App<F, X> = <F as AstTy>::TyCons<X>;

/* --- AST --- */

type Stmt = StmtF<Fix<TyParam>>;
enum StmtF<F: AstTy> {
    Block(App<F, BlockStmtF<TyParam>>),
    Expr(App<F, ExprF<TyParam>>),
    If(App<F, IfStmtF<TyParam>>),
    Let(App<F, LetStmtF<TyParam>>),
    Return(App<F, ReturnStmtF<TyParam>>),
    /*...*/
}

type BlockStmt = BlockStmtF<Fix<TyParam>>;
struct BlockStmtF<F: AstTy> {
    span: Span,
    stmts: Vec<App<F, StmtF<TyParam>>>,
}

type IfStmt = IfStmtF<Fix<TyParam>>;
struct IfStmtF<F: AstTy> {
    span: Span,
    cond: App<F, ExprF<TyParam>>,
    then_block: App<F, BlockStmtF<TyParam>>,
    else_block: Option<App<F, BlockStmtF<TyParam>>>,
}

type LetStmt = LetStmtF<Fix<TyParam>>;
struct LetStmtF<F: AstTy> {
    span: Span,
    ident: Ident,
    init: App<F, ExprF<TyParam>>,
}

type ReturnStmt = ReturnStmtF<Fix<TyParam>>;
struct ReturnStmtF<F: AstTy> {
    span: Span,
    expr: App<F, ExprF<TyParam>>,
}

type Expr = ExprF<Fix<TyParam>>;
enum ExprF<F: AstTy> {
    Ident(Ident),
    Add(Box<App<F, ExprF<TyParam>>>, Box<App<F, ExprF<TyParam>>>),
    NumLit(i64),
    /*...*/
}

#[derive(Debug, Clone, Copy)]
struct Span;
type Ident = String;

/* --- trait impl for AST nodes --- */

impl AstNode for StmtF<TyParam> {
    type TyCons<F: AstTy> = StmtF<F>;
}

impl AstFunctor for StmtF<TyParam> {
    fn fmap<F, U, G>(f: F, x: StmtF<U>) -> StmtF<G>
    where
        F: AstNodeMapFn<U, G>,
        U: AstTy,
        G: AstTy,
    {
        use StmtF::*;

        match x {
            Block(inner) => Block(f.call(inner)),
            Expr(inner) => Expr(f.call(inner)),
            If(inner) => If(f.call(inner)),
            Let(inner) => Let(f.call(inner)),
            Return(inner) => Return(f.call(inner)),
        }
    }
}

impl AstNode for BlockStmtF<TyParam> {
    type TyCons<F: AstTy> = BlockStmtF<F>;
}

impl AstFunctor for BlockStmtF<TyParam> {
    fn fmap<F, U, G>(f: F, x: BlockStmtF<U>) -> BlockStmtF<G>
    where
        F: AstNodeMapFn<U, G>,
        U: AstTy,
        G: AstTy,
    {
        let BlockStmtF { span, stmts } = x;
        BlockStmtF {
            span,
            stmts: stmts
                .into_iter()
                .map(|stmt| f.call(stmt))
                .collect(),
        }
    }
}

impl AstNode for IfStmtF<TyParam> {
    type TyCons<F: AstTy> = IfStmtF<F>;
}

impl AstFunctor for IfStmtF<TyParam> {
    fn fmap<F, U, G>(f: F, x: IfStmtF<U>) -> IfStmtF<G>
    where
        F: AstNodeMapFn<U, G>,
        U: AstTy,
        G: AstTy,
    {
        let IfStmtF { span, cond, then_block, else_block } = x;
        IfStmtF {
            span,
            cond: f.call(cond),
            then_block: f.call(then_block),
            else_block: else_block.map(|block| f.call(block)),
        }
    }
}

impl AstNode for LetStmtF<TyParam> {
    type TyCons<F: AstTy> = LetStmtF<F>;
}

impl AstFunctor for LetStmtF<TyParam> {
    fn fmap<F, U, G>(f: F, x: LetStmtF<U>) -> LetStmtF<G>
    where
        F: AstNodeMapFn<U, G>,
        U: AstTy,
        G: AstTy,
    {
        let LetStmtF { span, ident, init } = x;
        LetStmtF {
            span,
            ident,
            init: f.call(init),
        }
    }
}

impl AstNode for ReturnStmtF<TyParam> {
    type TyCons<F: AstTy> = ReturnStmtF<F>;
}

impl AstFunctor for ReturnStmtF<TyParam> {
    fn fmap<F, U, G>(f: F, x: ReturnStmtF<U>) -> ReturnStmtF<G>
    where
        F: AstNodeMapFn<U, G>,
        U: AstTy,
        G: AstTy,
    {
        let ReturnStmtF { span, expr } = x;
        ReturnStmtF {
            span,
            expr: f.call(expr),
        }
    }
}

impl AstNode for ExprF<TyParam> {
    type TyCons<F: AstTy> = ExprF<F>;
}

impl AstFunctor for ExprF<TyParam> {
    fn fmap<F, U, G>(f: F, x: ExprF<U>) -> ExprF<G>
    where
        F: AstNodeMapFn<U, G>,
        U: AstTy,
        G: AstTy,
    {
        use ExprF::*;

        match x {
            Ident(ident) => Ident(ident),
            Add(lhs, rhs) => Add(Box::new(f.call(*lhs)), Box::new(f.call(*rhs))),
            NumLit(lit) => NumLit(lit),
        }
    }
}

impl<T: AstNode> AstNode for Box<T> {
    type TyCons<F: AstTy> = Box<T::TyCons<F>>;
}

impl<T: AstFunctor> AstFunctor for Box<T> {
    fn fmap<F, U, G>(f: F, x: Box<T::TyCons<U>>) -> Box<T::TyCons<G>>
    where
        F: AstNodeMapFn<U, G>,
        U: AstTy,
        G: AstTy,
    {
        Box::new(T::fmap(f, *x))
    }
}

/* --- more trait impls that the derive macro can't auto implement correctly --- */

impl<F: AstTy> Clone for StmtF<F> {
    fn clone(&self) -> Self {
        use StmtF::*;

        match self {
            Block(inner) => Block(inner.clone()),
            Expr(inner) => Expr(inner.clone()),
            If(inner) => If(inner.clone()),
            Let(inner) => Let(inner.clone()),
            Return(inner) => Return(inner.clone()),
        }
    }
}

impl<F: AstTy> Clone for BlockStmtF<F> {
    fn clone(&self) -> Self {
        BlockStmtF {
            span: self.span,
            stmts: self.stmts.clone(),
        }
    }
}

impl<F: AstTy> Clone for IfStmtF<F> {
    fn clone(&self) -> Self {
        IfStmtF {
            span: self.span,
            cond: self.cond.clone(),
            then_block: self.then_block.clone(),
            else_block: self.else_block.clone(),
        }
    }
}

impl<F: AstTy> Clone for LetStmtF<F> {
    fn clone(&self) -> Self {
        LetStmtF {
            span: self.span,
            ident: self.ident.clone(),
            init: self.init.clone(),
        }
    }
}

impl<F: AstTy> Clone for ReturnStmtF<F> {
    fn clone(&self) -> Self {
        ReturnStmtF {
            span: self.span,
            expr: self.expr.clone(),
        }
    }
}

impl<F: AstTy> Clone for ExprF<F> {
    fn clone(&self) -> Self {
        use ExprF::*;

        match self {
            Ident(ident) => Ident(ident.clone()),
            Add(lhs, rhs) => Add(lhs.clone(), rhs.clone()),
            NumLit(lit) => NumLit(lit.clone()),
        }
    }
}

/* --- helper --- */

// The fixpoint type
#[repr(transparent)]
struct Fix<N: AstNode>(N::TyCons<Fix<TyParam>>);

impl<N: AstFunctor> Fix<N> {
    fn new(inner: N::TyCons<Fix<TyParam>>) -> Self {
        Self(inner)
    }

    fn out(self) -> N::TyCons<Fix<TyParam>> {
        self.0
    }
}

fn fix<N: AstFunctor>(inner: N::TyCons<Fix<TyParam>>) -> Fix<N> {
    Fix::new(inner)
}

impl AstTy for Fix<TyParam> {
    type TyCons<N: AstNode> = Fix<N>;
}

impl<N: AstNode> Clone for Fix<N> {
    fn clone(&self) -> Self {
        Fix(self.0.clone())
    }
}

// The singleton type of AST nodes
enum SAstNode<N: AstFunctor> {
    Stmt(TEq<N, StmtF<TyParam>>),
    BlockStmt(TEq<N, BlockStmtF<TyParam>>),
    IfStmt(TEq<N, IfStmtF<TyParam>>),
    LetStmt(TEq<N, LetStmtF<TyParam>>),
    ReturnStmt(TEq<N, ReturnStmtF<TyParam>>),
    Expr(TEq<N, ExprF<TyParam>>),
}

impl<N: AstFunctor + 'static> SAstNode<N> {
    fn new() -> Self {
        let id = TypeId::of::<N>();
        if id == TypeId::of::<StmtF<TyParam>>() {
            unsafe { SAstNode::Stmt(TEq::sorry()) }
        } else if id == TypeId::of::<BlockStmtF<TyParam>>() {
            unsafe { SAstNode::BlockStmt(TEq::sorry()) }
        } else if id == TypeId::of::<IfStmtF<TyParam>>() {
            unsafe { SAstNode::IfStmt(TEq::sorry()) }
        } else if id == TypeId::of::<LetStmtF<TyParam>>() {
            unsafe { SAstNode::LetStmt(TEq::sorry()) }
        } else if id == TypeId::of::<ReturnStmtF<TyParam>>() {
            unsafe { SAstNode::ReturnStmt(TEq::sorry()) }
        } else if id == TypeId::of::<ExprF<TyParam>>() {
            unsafe { SAstNode::Expr(TEq::sorry()) }
        } else {
            unreachable!()
        }
    }
}

/* --- type equality proofs --- */

/// Proof that the types `A` and `B` are the same type
struct TEq<A, B>(PhantomData<fn(A, B) -> (A, B)>);

impl<T> TEq<T, T> {
    // Only way to safely construct this
    fn refl() -> Self {
        TEq(PhantomData)
    }
}

impl<A, B> TEq<A, B> {
    unsafe fn sorry() -> Self {
        TEq(PhantomData)
    }

    // A better name might be `refine`, or `cast_with`.
    fn transmute(self, value: A) -> B {
        // SAFETY: `self` is proof that `A` and `B` are the same type
        unsafe {
            let b = std::mem::transmute_copy::<A, B>(&value);
            std::mem::forget(value);
            b
        }
    }

    fn to_ref<'a>(self) -> TEq<&'a A, &'a B> {
        TEq(PhantomData)
    }

    fn swap(self) -> TEq<B, A> {
        // Just using the reflexivity
        TEq(PhantomData)
    }
}

impl<A: AstFunctor, B: AstFunctor> TEq<A, B> {
    fn transmute_hkt<T: AstTy>(self, value: A::TyCons<T>) -> B::TyCons<T> {
        // SAFETY: `self` is proof that `A` and `B` are the same type
        unsafe {
            let b = std::mem::transmute_copy::<A::TyCons<T>, B::TyCons<T>>(&value);
            std::mem::forget(value);
            b
        }
    }
}

impl<A, B> Clone for TEq<A, B> {
    fn clone(&self) -> Self {
        TEq(PhantomData)
    }
}

impl<A, B> Copy for TEq<A, B> { }
