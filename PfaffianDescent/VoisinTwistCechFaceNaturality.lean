import PfaffianDescent.VoisinTwistCechNaturality
import PfaffianDescent.VoisinTwistCechDifferential

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open CategoryTheory.Limits
open scoped AddMonoidAlgebra BigOperators
universe u
namespace PfaffianDescent.ProjectiveNegativeTwist

open LaurentLocalization TwistLaurent TwistCechTerms
open TwistCechTerms.GenericEvaluation

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Transport a summand of the categorical Cech term to sections on its
canonical denominator basic open, before choosing a twist trivialization. -/
noncomputable def p3CechTermToBasic (m n : ℕ)
    (f : Fin (n + 1) → Fin 4) :
    p3CechTermFamily K m n f ⟶
      (modulePresheaf PS m).presheaf.obj
        (op (cechBasicOpen K n f)) :=
  ((modulePresheaf PS m).presheaf.mapIso
      (eqToIso (p3CechProduct_eq_inf K n f)).op.symm).hom ≫
    ((modulePresheaf PS m).presheaf.mapIso
      (eqToIso (p3CechBasicOpen_eq_inf (K := K) n f)).op).hom

lemma p3CechTermComponentIsoAway_hom (m n : ℕ)
    (f : Fin (n + 1) → Fin 4) :
    (p3CechTermComponentIsoAway K m n f).hom =
      p3CechTermToBasic K m n f ≫
        (p3NegativeTwistBasicOpenIsoAway K
          (p3CechDenominator (K := K) n f) (n + 1)
          (p3CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
          (f 0) (p3Coordinate_zero_dvd_cechDenominator (K := K) n f) m).hom := by
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma p3CechTermToBasic_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4) :
    let E := (CategoryTheory.Limits.FormalCoproduct.mk _
      (p3StandardOpen (K := K))).cech
    let P := (modulePresheaf PS m).presheaf
    let hx := p3CechDenominator_succ_eq_deleteTuple_mul
      (K := K) n i f
    let hST : cechBasicOpen K (n + 1) f ≤
        cechBasicOpen K n (deleteTuple i f) :=
      AlgebraicGeometry.Proj.basicOpen_mono PS
        (p3CechDenominator (K := K) n (deleteTuple i f))
        (p3CechDenominator (K := K) (n + 1) f) ⟨_, hx⟩
    P.map ((E.map (SimplexCategory.δ i).op).φ f).op ≫
        p3CechTermToBasic K m (n + 1) f =
      p3CechTermToBasic K m n (deleteTuple i f) ≫
        P.map (homOfLE hST).op := by
  dsimp only
  simp only [p3CechTermToBasic, Functor.mapIso_hom, Category.assoc]
  rw [← (modulePresheaf PS m).presheaf.map_comp,
    ← (modulePresheaf PS m).presheaf.map_comp,
    ← (modulePresheaf PS m).presheaf.map_comp,
    ← (modulePresheaf PS m).presheaf.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
lemma twistAwayToLaurent_restrict_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4)
    (s : Γ(sheafOfModules PS m,
      cechBasicOpen K n (deleteTuple i f))) :
    let hS := p3Coordinate_zero_dvd_cechDenominator
      (K := K) n (deleteTuple i f)
    let hT := p3Coordinate_zero_dvd_cechDenominator (K := K) (n + 1) f
    let hx := p3CechDenominator_succ_eq_deleteTuple_mul
      (K := K) n i f
    let hST : cechBasicOpen K (n + 1) f ≤
        cechBasicOpen K n (deleteTuple i f) :=
      AlgebraicGeometry.Proj.basicOpen_mono PS
        (p3CechDenominator (K := K) n (deleteTuple i f))
        (p3CechDenominator (K := K) (n + 1) f) ⟨_, hx⟩
    let sT : Γ(sheafOfModules PS m, cechBasicOpen K (n + 1) f) :=
      (sheafOfModules PS m).presheaf.map (homOfLE hST).op s
    twistAwayToLaurent (K := K) m (n + 1) f
        (chartAway K (n + 1) f m (f 0) hT sT) =
      twistAwayToLaurent (K := K) m n (deleteTuple i f)
        (chartAway K n (deleteTuple i f) m
          ((deleteTuple i f) 0) hS s) := by
  dsimp only
  let del := deleteTuple i f
  let denS := p3CechDenominator (K := K) n del
  let denT := p3CechDenominator (K := K) (n + 1) f
  let hx : denT = denS * MvPolynomial.X (R := K) (f i) :=
    p3CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f
  let hS := p3Coordinate_zero_dvd_cechDenominator (K := K) n del
  let hT := p3Coordinate_zero_dvd_cechDenominator (K := K) (n + 1) f
  let hAlt : MvPolynomial.X (R := K) (del 0) ∣ denT :=
    dvd_trans hS ⟨_, hx⟩
  let hST : cechBasicOpen K (n + 1) f ≤ cechBasicOpen K n del :=
    AlgebraicGeometry.Proj.basicOpen_mono PS denS denT ⟨_, hx⟩
  let sT : Γ(sheafOfModules PS m, cechBasicOpen K (n + 1) f) :=
    (sheafOfModules PS m).presheaf.map (homOfLE hST).op s
  let zS := chartAway K n del m (del 0) hS s
  let zAlt := chartAway K (n + 1) f m (del 0) hAlt sT
  let zT := chartAway K (n + 1) f m (f 0) hT sT
  have hnat := negativeTwistBasicOpenIsoAway_natural K
    denS (MvPolynomial.X (R := K) (f i)) denT (n + 1) 1
    (p3CechDenominator_mem (K := K) n del)
    (coordinate_mem_degree_one (K := K) (f i)) (Nat.succ_pos n) hx
    (del 0) hS m
  have hres : zAlt = awayFaceMap (K := K) n i f zS := by
    have happ := congrArg (fun q => q s) hnat
    simp only [ConcreteCategory.comp_apply] at happ
    change _ = _
    convert happ using 1
    rfl
  have hchart := twistAwayToLaurent_chart_independent K (n + 1) f m
    (f 0) hT (del 0) hAlt sT
  change awayToLaurent (K := K) (n + 1) f zT *
      AddMonoidAlgebra.single (twistShift m (f 0)) 1 =
    awayToLaurent (K := K) n del zS *
      AddMonoidAlgebra.single (twistShift m (del 0)) 1
  calc
    _ = awayToLaurent (K := K) (n + 1) f zAlt *
        AddMonoidAlgebra.single (twistShift m (del 0)) 1 := hchart
    _ = awayToLaurent (K := K) (n + 1) f
          (awayFaceMap (K := K) n i f zS) *
        AddMonoidAlgebra.single (twistShift m (del 0)) 1 := by rw [hres]
    _ = _ := by rw [awayToLaurent_awayFaceMap]

set_option backward.isDefEq.respectTransparency false in
lemma p3CechTermComponentToLaurent_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4)
    (s : p3CechTermFamily K m n (deleteTuple i f)) :
    let E := (CategoryTheory.Limits.FormalCoproduct.mk _
      (p3StandardOpen (K := K))).cech
    let P := (modulePresheaf PS m).presheaf
    twistAwayToLaurent (K := K) m (n + 1) f
        ((p3CechTermComponentIsoAway K m (n + 1) f).hom
          (P.map ((E.map (SimplexCategory.δ i).op).φ f).op s)) =
      twistAwayToLaurent (K := K) m n (deleteTuple i f)
        ((p3CechTermComponentIsoAway K m n (deleteTuple i f)).hom s) := by
  dsimp only
  have hface := congrArg (fun q => q s)
    (p3CechTermToBasic_face K m n i f)
  simp only [ConcreteCategory.comp_apply] at hface
  simp only [p3CechTermComponentIsoAway_hom,
    ConcreteCategory.comp_apply]
  let targetIso := p3NegativeTwistBasicOpenIsoAway K
    (p3CechDenominator (K := K) (n + 1) f) ((n + 1) + 1)
    (p3CechDenominator_mem (K := K) (n + 1) f) (Nat.succ_pos (n + 1))
    (f 0) (p3Coordinate_zero_dvd_cechDenominator (K := K) (n + 1) f) m
  have hface' := congrArg
    (fun q => twistAwayToLaurent (K := K) m (n + 1) f (targetIso.hom q))
    hface
  calc
    _ = twistAwayToLaurent (K := K) m (n + 1) f
          (targetIso.hom
            ((modulePresheaf PS m).presheaf.map
              (homOfLE (AlgebraicGeometry.Proj.basicOpen_mono PS
                (p3CechDenominator (K := K) n (deleteTuple i f))
                (p3CechDenominator (K := K) (n + 1) f)
                ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul
                  (K := K) n i f⟩)).op
              (p3CechTermToBasic K m n (deleteTuple i f) s))) := hface'
    _ = _ := twistAwayToLaurent_restrict_face K m n i f
      (p3CechTermToBasic K m n (deleteTuple i f) s)

end PfaffianDescent.ProjectiveNegativeTwist
