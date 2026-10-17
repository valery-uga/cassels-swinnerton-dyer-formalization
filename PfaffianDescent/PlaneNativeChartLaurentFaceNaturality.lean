import PfaffianDescent.PlanePositiveChartGenericNaturality
/-! SOURCE ONLY / UNCHECKED. The native positive and negative chart Laurent maps
commute with every original coordinate-cover face restriction, including
change of first chart coordinate. No face equality certificate is assumed. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open ProjectiveNegativeTwist PlaneLaurentLocalization PlaneTwistLaurent
open PlaneTwistCechTerms PlaneTwistCechTerms.GenericEvaluation PlanePositiveTwistNaturality
open scoped AddMonoidAlgebra BigOperators
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K
set_option backward.isDefEq.respectTransparency false in
lemma twistAwayToLaurent_restrict_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3)
    (s : Γ(sheafOfModules PS m,
      p2CechBasicOpen K n (deleteTuple i f))) :
    let hS := p2Coordinate_zero_dvd_cechDenominator
      (K := K) n (deleteTuple i f)
    let hT := p2Coordinate_zero_dvd_cechDenominator (K := K) (n + 1) f
    let hx := p2CechDenominator_succ_eq_deleteTuple_mul
      (K := K) n i f
    let hST : p2CechBasicOpen K (n + 1) f ≤
        p2CechBasicOpen K n (deleteTuple i f) :=
      AlgebraicGeometry.Proj.basicOpen_mono PS
        (p2CechDenominator (K := K) n (deleteTuple i f))
        (p2CechDenominator (K := K) (n + 1) f) ⟨_, hx⟩
    let sT : Γ(sheafOfModules PS m, p2CechBasicOpen K (n + 1) f) :=
      (sheafOfModules PS m).presheaf.map (homOfLE hST).op s
    twistAwayToLaurent (K := K) m (n + 1) f
        (chartAway K (n + 1) f m (f 0) hT sT) =
      twistAwayToLaurent (K := K) m n (deleteTuple i f)
        (chartAway K n (deleteTuple i f) m
          ((deleteTuple i f) 0) hS s) := by
  dsimp only
  let del := deleteTuple i f
  let denS := p2CechDenominator (K := K) n del
  let denT := p2CechDenominator (K := K) (n + 1) f
  let hx : denT = denS * MvPolynomial.X (R := K) (f i) :=
    p2CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f
  let hS := p2Coordinate_zero_dvd_cechDenominator (K := K) n del
  let hT := p2Coordinate_zero_dvd_cechDenominator (K := K) (n + 1) f
  let hAlt : MvPolynomial.X (R := K) (del 0) ∣ denT :=
    dvd_trans hS ⟨_, hx⟩
  let hST : p2CechBasicOpen K (n + 1) f ≤ p2CechBasicOpen K n del :=
    AlgebraicGeometry.Proj.basicOpen_mono PS denS denT ⟨_, hx⟩
  let sT : Γ(sheafOfModules PS m, p2CechBasicOpen K (n + 1) f) :=
    (sheafOfModules PS m).presheaf.map (homOfLE hST).op s
  let zS := chartAway K n del m (del 0) hS s
  let zAlt := chartAway K (n + 1) f m (del 0) hAlt sT
  let zT := chartAway K (n + 1) f m (f 0) hT sT
  have hnat := negativeTwistBasicOpenIsoAway_natural K
    denS (MvPolynomial.X (R := K) (f i)) denT (n + 1) 1
    (p2CechDenominator_mem (K := K) n del)
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


/-- Actual positive-sheaf restriction along a coordinate-cover face is the
SAME Laurent representative. Both chart frames are internally derived. -/
theorem p2PositiveNativeChartToLaurent_restrict_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3)
    (s : Γ(positiveSheafOfModules PS m, p2CechBasicOpen K n (deleteTuple i f))) :
    let hST : p2CechBasicOpen K (n + 1) f ≤ p2CechBasicOpen K n (deleteTuple i f) :=
      AlgebraicGeometry.Proj.basicOpen_mono PS
        (p2CechDenominator (K := K) n (deleteTuple i f))
        (p2CechDenominator (K := K) (n + 1) f)
        ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
    p2PositiveNativeChartToLaurent K m (n + 1) f
        ((positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op s) =
      p2PositiveNativeChartToLaurent K m n (deleteTuple i f) s := by
  dsimp only
  let del := deleteTuple i f
  let hx := p2CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f
  let hdiv := dvd_trans (p2Coordinate_zero_dvd_cechDenominator (K := K) n del) ⟨_, hx⟩
  let hST : p2CechBasicOpen K (n + 1) f ≤ p2CechBasicOpen K n del :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (p2CechDenominator (K := K) n del) (p2CechDenominator (K := K) (n + 1) f) ⟨_, hx⟩
  let sT := (positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op s
  have hind := p2PositiveTwistChartLaurent_independent K (n + 1) f m
    (f 0) (p2Coordinate_zero_dvd_cechDenominator (K := K) (n + 1) f)
    (del 0) hdiv sT
  have hface := p2PositiveTwistChartLaurent_restrict_face K m n i f s
  calc
    p2PositiveNativeChartToLaurent K m (n + 1) f sT =
        awayToLaurent (K := K) (n + 1) f
          (p2PositiveTwistChartAway K (n + 1) f m (del 0) hdiv sT) *
          AddMonoidAlgebra.single (positiveTwistShift m (del 0)) 1 := hind
    _ = awayToLaurent (K := K) n del
          (p2PositiveTwistChartAway K n del m (del 0)
            (p2Coordinate_zero_dvd_cechDenominator (K := K) n del) s) *
          AddMonoidAlgebra.single (positiveTwistShift m (del 0)) 1 :=
      congrArg (fun z => z * AddMonoidAlgebra.single (positiveTwistShift m (del 0)) 1) hface
    _ = p2PositiveNativeChartToLaurent K m n del s := rfl


/-- Actual SAME negative native chart map, including the internally derived
change of chart coordinate, is preserved under every native face. -/
theorem p2NegativeNativeChartToLaurent_restrict_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3)
    (s : Γ(sheafOfModules PS m, p2CechBasicOpen K n (deleteTuple i f))) :
    let hST : p2CechBasicOpen K (n + 1) f ≤ p2CechBasicOpen K n (deleteTuple i f) :=
      Proj.basicOpen_mono PS (p2CechDenominator (K := K) n (deleteTuple i f))
        (p2CechDenominator (K := K) (n + 1) f)
        ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
    p2NegativeNativeChartToLaurent K m (n + 1) f
        ((sheafOfModules PS m).presheaf.map (homOfLE hST).op s) =
      p2NegativeNativeChartToLaurent K m n (deleteTuple i f) s := by
  exact twistAwayToLaurent_restrict_face K m n i f s

end PfaffianDescent.ProjectivePlaneNative
