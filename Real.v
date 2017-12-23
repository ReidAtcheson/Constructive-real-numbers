Require Import QArith.QArith_base.
Require Import QArith.Qabs.
Require Import QArith.Qpower.
Require Import QArith.Qround.
Require Import ZArith.Znat.
Require Import Psatz.
Require Import Init.Nat.
Require Import Omega.
Require Extraction.

Module Type Sig.

Parameter R : Type.
Parameter Rzero : R.
Parameter Rone : R.
Parameter Req : R -> R -> Prop.
Parameter Rlt : R -> R -> Prop.
Parameter Radd : R -> R -> R.
Parameter Radd_inv : R -> R.
Parameter Rmult : R -> R -> R.
Parameter Rmult_inv  : R -> R.
(*Req is an equivalence relation.*)
Axiom Req_refl : forall (r:R), Req r r.
Axiom Req_trans : forall (r1 r2 r3:R), Req r1 r2 -> Req r2 r3 -> Req r1 r3.
Axiom Req_symm : forall (r1 r2:R), Req r1 r2 -> Req r2 r1.


(*Radd,Radd_inv,Req forms a commutative group*)
Axiom Radd_commutative : forall (r1 r2:R), Req (Radd r1 r2) (Radd r2 r1).
Axiom Radd_associative : forall (r1 r2 r3:R), Req (Radd r1 (Radd r2 r3)) (Radd (Radd r1 r2) r3).
Axiom Radd_inv_compat  : forall (r:R), Req (Radd r (Radd_inv r)) Rzero.


(*Rmult,Rmult_inv form commutative semigroup*)
Axiom Rmult_commutative : forall (r1 r2:R), Req (Rmult r1 r2) (Rmult r2 r1).
Axiom Rmult_associative : forall (r1 r2 r3:R), Req (Rmult r1 (Rmult r2 r3)) (Rmult (Rmult r1 r2) r3).
Axiom Rmult_inv_compat : forall r, (not (Req r Rzero)) -> Req (Rmult r (Rmult_inv r)) Rone.

(*Radd,Rmult,Radd_inv,Rmult_inv,Req form field*)

Axiom Rmult_distributes_Radd : forall (a b c:R), Req (Rmult (Radd a b) c) (Radd (Rmult a c) (Rmult b c)).




End Sig.



Definition Cauchy (F:Q->Q) := forall err err1 err2, err>0 -> err1>0 -> err2>0 ->
          err1<err -> err2<err ->
          ((Qabs ((F err1) - (F err2))) < err).

Definition R := { F:Q->Q | Cauchy F}.




Lemma Qabs_extensional : forall q1 q2, q1==q2 -> Qabs q1 == Qabs q2.
Proof.
intros.
destruct q1. destruct q2.
unfold Qabs. unfold Z.abs.
destruct Qnum, Qnum0.
* lra.
* auto.
* assert( not (0 # Qden == Z.neg p # Qden0) ).
** unfold Qeq. assert( (Qnum (0 # Qden) = 0)%Z ) by auto with *.
   rewrite H. auto with *.
** contradiction.
* auto.
* auto. 
* assert( not (Zpos p # Qden == Z.neg p0 # Qden0) ).
** unfold Qeq. auto with *.
** contradiction.
* assert( not (Z.neg p # Qden == 0 # Qden0) ).
** unfold Qeq. auto with *.
** contradiction.
* assert( not ( Z.neg p # Qden == ' p0 # Qden0) ).
** unfold Qeq. auto with *.
** contradiction.
* unfold Qeq. unfold Qeq in H. simpl. simpl in H.
  assert ( (p*Qden0 = p0*Qden)%positive ).
** nia.
** rewrite H0. auto with *.

Qed.

Definition injectQ (q:Q) : R.
Proof.
unfold R.
exists (fun err =>q ).
unfold Cauchy.
intros.
assert( Qabs(q-q) == Qabs(0) ).
{
  apply Qabs_extensional. lra.
}
rewrite H4.
simpl.
lra.
Defined.

Definition oneR := injectQ 1.
Definition zeroR := injectQ 0.
Definition twoR := injectQ (1+1).

Definition Rplus (r1:R) (r2:R) : R.
Proof.
apply (Rmake (fun q => (F r1) (q*(1#2)) + (F r2) (q*(1#2)))).
intros.
remember (F r1 (err1 * (1 # 2))) as x.
remember (F r2 (err1 * (1 # 2))) as y.
remember (F r1 (err2 * (1 # 2))) as z.
remember (F r2 (err2 * (1 # 2))) as u.
assert( Qabs( x + y - (z+u) ) == Qabs((x-z) + (y-u)) ).
{
  apply (Qabs_extensional).
  field.
}  
rewrite H4.
assert( Qabs (x-z +y-u) <= Qabs (x-z) + Qabs(y-u) ).
{
  assert( Qabs (x-z+y-u) == Qabs( (x-z) + (y-u) )).
  {
    apply Qabs_extensional. field.
  }
  rewrite H5.
  apply Qabs_triangle.
}
assert( Qabs (x-z) < err * (1#2) ).
{
  rewrite Heqx. rewrite Heqz.
  apply ((Cauchy r1) (err*(1#2)) (err1*(1#2)) (err2*(1#2))).
  * lra.
  * lra.
  * lra.
  * lra.
  * lra.
}
assert( Qabs (y-u) < err*(1#2) ).
{
  rewrite Heqy. rewrite Hequ.
  apply ((Cauchy r2) (err*(1#2)) (err1*(1#2)) (err2*(1#2))).
  * lra.
  * lra. 
  * lra.
  * lra.
  * lra.
}
assert( (Qabs (x - z) + Qabs (y - u)) < err ) by lra.
assert( Qabs (x - z + y - u) == Qabs( x - z + (y-u) )).
{
  apply Qabs_extensional.
  field.
}
rewrite H9 in H5.
lra.
Defined.

Definition Req (r1 r2 : R):= {c | forall q, q>0 -> Qabs( (F r1) q - (F r2) q) < c*q}.

Theorem z_not_eq_1 : (Req zeroR oneR) -> False.


Theorem req_works : Req oneR oneR.
Proof.
unfold Req.
exists 1.
intros.
unfold oneR.
simpl.
lra.
Qed.

Theorem req_refl : forall (r:R), Req r r.
Proof.
intros.
unfold Req.
exists 1.
intros.
remember (F r q) as z.
assert(Qabs (z-z)==Qabs 0).
{
  assert((z-z)==0) by field.
  apply (Qabs_extensional (z-z)). auto.
}
rewrite H0.
simpl. lra.
Qed.

Theorem req_trans : forall (r1 r2 r3:R), Req r1 r2 -> Req r2 r3 -> Req r1 r3.
Proof.
intros.
unfold Req in H.
unfold Req in H0.
destruct H.
destruct H0.
unfold Req.
exists (x+x0).
intros.
remember (F r1 q1) as z1.
remember (F r3 q1) as z3.
remember (F r2 q1) as z2.
assert( Qabs(z1 - z3) == Qabs( (z1 - z2) + (z2 - z3) ) ).
{
  apply Qabs_extensional.
  field.
}
rewrite H0.
assert( Qabs (z1-z2 + (z2-z3)) <= Qabs (z1-z2) + Qabs (z2-z3) ) by apply Qabs_triangle.
assert(Qabs(z1-z2) < x * q1).
{
  rewrite Heqz1.
  rewrite Heqz2.
  apply (q q1 H).
}
assert(Qabs(z2-z3) < x0*q1).
{
  rewrite Heqz2. rewrite Heqz3.
  apply (q0 q1 H).
}
assert( Qabs (z1 - z2) + Qabs (z2 - z3) < (x+x0)*q1 ) by lra.
lra.
Qed.

Theorem req_symm : forall (r1 r2 : R), Req r1 r2 -> Req r2 r1.
Proof.
intros.
unfold Req.
unfold Req in H.
destruct H.
exists x.
intros.
remember (F r1 q0) as z1.
remember (F r2 q0) as z2.
assert( Qabs(z2 - z1) == Qabs (z1 - z2) ).
{
  assert(Qabs (z2-z1) == Qabs ( -(z1-z2) ) ).
  {
    apply Qabs_extensional. field.
  }
  rewrite H0.
  apply Qabs_opp.
}
rewrite H0.
rewrite Heqz1.
rewrite Heqz2.
apply (q q0 H).
Qed.

Theorem rplus_req_compat : forall (r1 r2 : R), Req (Rplus r1 r2) (Rplus r2 r1).
Proof.
intros.
unfold Req.
exists 1.
intros.
unfold Rplus. simpl. remember (q*(1#2)) as p.
remember (Qnum (F r1 p)) as z1.
remember (Zpos (Qden (F r2 p))) as z2.
remember (Qnum (F r2 p)) as z3.
remember (Zpos (Qden (F r1 p))) as z4.
remember (Zpos (Qden (F r2 p))) as z5.
assert( (' (Qden (F r2 p) * Qden (F r1 p)) = z4*z5)%Z ).
{
  nia.
}
rewrite H0.
assert( (Zpos (Qden (F r1 p) * Qden (F r2 p)) = z4*z5)%Z ).
{
  nia.
}
rewrite H1.
assert( (((z1 * z2 + z3 * z4) * (z4 * z5) +
   - (z3 * z4 + z1 * z2) * (z4 * z5)) = 0)%Z ) by nia.
rewrite H2.
simpl.
assert( 0
# Qden (F r1 p) * Qden (F r2 p) *
  (Qden (F r2 p) * Qden (F r1 p)) == 0).
{
  unfold Qeq. simpl. auto.
}
rewrite H3.
lra.

Qed.


Definition Rmult (r1 r2:R) : R.
Proof.
apply (Rmake (fun q => (F r1 q)*(F r2 q) ) ).
intros.
remember (F r1 err1) as z11.
remember (F r2 err1) as z21.
remember (F r1 err2) as z12.
remember (F r2 err2) as z22.
Admitted.

Module ConReal <: Sig.
Definition R:= R.
End ConReal.


Eval vm_compute in (F (Rplus oneR oneR)).