Require Import QArith.QArith_base.
Require Import QArith.Qabs.
Require Import QArith.Qpower.
Require Import QArith.Qround.
Require Import ZArith.Znat.
Require Import Psatz.
Require Import Init.Nat.
Require Import Omega.


Record R : Set := Rmake { 
F : (Q->Q);
Cauchy : (forall err err1 err2, err>0 -> err1>0 -> err2>0 ->
          err1<err -> err2<err ->
          ((Qabs ((F err1) - (F err2))) < err) )
}.


Definition oneRF (q:Q) := 1#1.

Definition oneR : R.
Proof.
apply (Rmake oneRF).
intros.
unfold oneRF.
simpl.
lra.
Qed.

Eval compute in oneR.

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
  assert( 0<err1*(1#2) ) by lra.
  assert( 0<err2*(1#2) ) by lra.
  assert( 0<err*(1#2) ) by lra.
  assert( err1*(1#2) < err*(1#2) ) by lra.
  assert( err2*(1#2) < err*(1#2) ) by lra.
  apply ((Cauchy r1) (err*(1#2)) (err1*(1#2)) (err2*(1#2))).
  * auto.
  * auto.
  * auto.
  * auto.
  * auto.  
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


Eval vm_compute in (Rplus oneR oneR).
