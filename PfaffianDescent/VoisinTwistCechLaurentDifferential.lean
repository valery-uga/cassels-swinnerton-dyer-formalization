import PfaffianDescent.VoisinTwistCechFaceNaturality

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open CategoryTheory.Limits
open scoped AddMonoidAlgebra BigOperators
universe u
namespace PfaffianDescent.ProjectiveNegativeTwist

open LaurentLocalization LaurentCechCore TwistLaurent TwistCechTerms

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

lemma p3NegativeTwistCechTermToLaurent_coface
    (m n : ℕ) (i : Fin (n + 2))
    (x : (p3NegativeTwistCechComplex (K := K) m).X n)
    (f : Fin (n + 2) → Fin 4) :
    p3NegativeTwistCechTermToLaurent K m (n + 1)
        ((p3CechCosimplicial K m).δ i x) f =
      p3NegativeTwistCechTermToLaurent K m n x (deleteTuple i f) := by
  change twistAwayToLaurent (K := K) m (n + 1) f
      (p3NegativeTwistCechTermAddEquivAway K m (n + 1)
        ((p3CechCosimplicial K m).δ i x) f) =
    twistAwayToLaurent (K := K) m n (deleteTuple i f)
      (p3NegativeTwistCechTermAddEquivAway K m n x (deleteTuple i f))
  let y : (p3NegativeTwistCechComplex (K := K) m).X (n + 1) :=
    (p3CechCosimplicial K m).δ i x
  change twistAwayToLaurent (K := K) m (n + 1) f
      (p3NegativeTwistCechTermAddEquivAway K m (n + 1) y f) = _
  rw [p3NegativeTwistCechTermAddEquivAway_apply K m (n + 1) y f,
    p3NegativeTwistCechTermAddEquivAway_apply K m n x (deleteTuple i f)]
  have hπ := ConcreteCategory.congr_hom
    (p3Cech_coface_comp_π K m n i f) x
  let E := (CategoryTheory.Limits.FormalCoproduct.mk _
    (p3StandardOpen (K := K))).cech
  let P := (modulePresheaf PS m).presheaf
  have hleft := ConcreteCategory.comp_apply
    ((p3CechCosimplicial K m).δ i)
    (Pi.π (fun j : (E.obj (Opposite.op (SimplexCategory.mk (n + 1)))).I =>
      P.obj (Opposite.op ((E.obj (Opposite.op
        (SimplexCategory.mk (n + 1)))).obj j))) f) x
  have hright := ConcreteCategory.comp_apply
    (Pi.π (fun j : (E.obj (Opposite.op (SimplexCategory.mk n))).I =>
      P.obj (Opposite.op ((E.obj (Opposite.op
        (SimplexCategory.mk n))).obj j))) (deleteTuple i f))
    (P.map ((E.map (SimplexCategory.δ i).op).φ f).op) x
  have hπraw := hleft.symm.trans (hπ.trans hright)
  have hπ' :
      (Pi.π (p3CechTermFamily K m (n + 1)) f) y =
        P.map ((E.map (SimplexCategory.δ i).op).φ f).op
          ((Pi.π (p3CechTermFamily K m n) (deleteTuple i f)) x) := by
    exact hπraw
  rw [hπ']
  exact p3CechTermComponentToLaurent_face K m n i f
    ((Pi.π (p3CechTermFamily K m n) (deleteTuple i f)) x)

end PfaffianDescent.ProjectiveNegativeTwist

namespace PfaffianDescent.ProjectiveNegativeTwist
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open CategoryTheory.Limits
open scoped AddMonoidAlgebra BigOperators
open LaurentLocalization LaurentCechCore TwistLaurent TwistCechTerms
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma addCommGrp_finset_sum_apply {ι : Type*} {X Y : AddCommGrpCat}
    (s : Finset ι) (g : ι → (X ⟶ Y)) (x : X) :
    (∑ i ∈ s, g i) x = ∑ i ∈ s, g i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert, ha, not_false_eq_true,
        AddCommGrpCat.hom_add_apply, ih]

lemma addCommGrp_zsmul_apply {X Y : AddCommGrpCat}
    (z : ℤ) (g : X ⟶ Y) (x : X) :
    (z • g) x = z • g x := by
  change (z • g.hom) x = _
  exact AddMonoidHom.zsmul_apply g.hom z x

lemma addCommGrp_finset_sum_zsmul_apply {ι : Type*} {X Y : AddCommGrpCat}
    (s : Finset ι) (z : ι → ℤ) (g : ι → (X ⟶ Y)) (x : X) :
    (∑ i ∈ s, z i • g i) x = ∑ i ∈ s, z i • g i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert, ha, not_false_eq_true,
        AddCommGrpCat.hom_add_apply, addCommGrp_zsmul_apply, ih]

lemma p3NegativeTwistCechComplex_d_succ (m n : ℕ) :
    (p3NegativeTwistCechComplex (K := K) m).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (p3CechCosimplicial K m) n := by
  simp [p3NegativeTwistCechComplex, CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    p3CechCosimplicial]
  congr

lemma p3NegativeTwistCechTermToLaurent_d
    (m n : ℕ) (x : (p3NegativeTwistCechComplex (K := K) m).X n) :
    p3NegativeTwistCechTermToLaurent K m (n + 1)
        ((p3NegativeTwistCechComplex (K := K) m).d n (n + 1) x) =
      fun f => ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        p3NegativeTwistCechTermToLaurent K m n x (deleteTuple i f) := by
  funext f
  rw [p3NegativeTwistCechComplex_d_succ K m n]
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  calc
    _ = p3NegativeTwistCechTermToLaurent K m (n + 1)
        (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          ((p3CechCosimplicial K m).δ i x)) f := by
      exact congrArg
        (fun q => p3NegativeTwistCechTermToLaurent K m (n + 1) q f)
        (addCommGrp_finset_sum_zsmul_apply Finset.univ
          (fun i : Fin (n + 2) => (-1 : ℤ) ^ (i : ℕ))
          (fun i => (p3CechCosimplicial K m).δ i) x)
    _ = (∑ i : Fin (n + 2),
          p3NegativeTwistCechTermToLaurent K m (n + 1)
            (((-1 : ℤ) ^ (i : ℕ)) •
              ((p3CechCosimplicial K m).δ i x))) f := by
      exact congrFun (map_sum
        (p3NegativeTwistCechTermToLaurent K m (n + 1))
        (fun i : Fin (n + 2) => ((-1 : ℤ) ^ (i : ℕ)) •
          ((p3CechCosimplicial K m).δ i x)) Finset.univ) f
    _ = _ := by
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      let v : (p3NegativeTwistCechComplex (K := K) m).X (n + 1) :=
        (p3CechCosimplicial K m).δ i x
      change p3NegativeTwistCechTermToLaurent K m (n + 1)
          (((-1 : ℤ) ^ (i : ℕ)) • v) f = _
      have hz := map_zsmul (p3NegativeTwistCechTermToLaurent K m (n + 1))
        ((-1 : ℤ) ^ (i : ℕ)) v
      calc
        _ = (((-1 : ℤ) ^ (i : ℕ)) •
            p3NegativeTwistCechTermToLaurent K m (n + 1) v) f :=
          congrFun hz f
        _ = ((-1 : ℤ) ^ (i : ℕ)) •
            p3NegativeTwistCechTermToLaurent K m (n + 1) v f := rfl
        _ = _ := congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
          (p3NegativeTwistCechTermToLaurent_coface K m n i x f)


end PfaffianDescent.ProjectiveNegativeTwist

namespace PfaffianDescent.ProjectiveNegativeTwist
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open CategoryTheory.Limits
open scoped AddMonoidAlgebra BigOperators
open LaurentCechCore AwayCechExact
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma p3NegativeTwistCechTermToLaurent_d_zero
    (m : ℕ) (x : (p3NegativeTwistCechComplex (K := K) m).X 0) :
    p3NegativeTwistCechTermToLaurent K m 1
        ((p3NegativeTwistCechComplex (K := K) m).d 0 1 x) =
      tupleD0 (p3NegativeTwistCechTermToLaurent K m 0 x) := by
  rw [p3NegativeTwistCechTermToLaurent_d K m 0 x]
  funext f
  simp [Fin.sum_univ_two, tupleD0, sub_eq_add_neg]

lemma p3NegativeTwistCechTermToLaurent_d_one
    (m : ℕ) (x : (p3NegativeTwistCechComplex (K := K) m).X 1) :
    p3NegativeTwistCechTermToLaurent K m 2
        ((p3NegativeTwistCechComplex (K := K) m).d 1 2 x) =
      tupleD1 (p3NegativeTwistCechTermToLaurent K m 1 x) := by
  rw [p3NegativeTwistCechTermToLaurent_d K m 1 x]
  funext f
  simp [Fin.sum_univ_three, tupleD1, sub_eq_add_neg]

lemma p3NegativeTwistCechTermToLaurent_d_two
    (m : ℕ) (x : (p3NegativeTwistCechComplex (K := K) m).X 2) :
    p3NegativeTwistCechTermToLaurent K m 3
        ((p3NegativeTwistCechComplex (K := K) m).d 2 3 x) =
      tupleD2 (p3NegativeTwistCechTermToLaurent K m 2 x) := by
  rw [p3NegativeTwistCechTermToLaurent_d K m 2 x]
  funext f
  simp [Fin.sum_univ_four, tupleD2, sub_eq_add_neg]
  norm_num

end PfaffianDescent.ProjectiveNegativeTwist
