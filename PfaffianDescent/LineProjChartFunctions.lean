import PfaffianDescent.LineGrassmannianProjCharts
import PfaffianDescent.GrassmannianChartFunctionsExt
import PfaffianDescent.LineChartSubmoduleEquality

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable (K : Type u) [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

lemma lineGrassmannianProjChartRingEquiv_symm_base (b : Bool) (k : K) :
    (lineGrassmannianProjChartRingEquiv K b).symm (chartBaseMap I₀ b k) = C k :=
  (congrArg (lineGrassmannianProjChartRingEquiv K b).symm
    (lineGrassmannianProjChartRingEquiv_C K b k).symm).trans
      ((lineGrassmannianProjChartRingEquiv K b).symm_apply_apply (C k))

lemma lineGrassmannianProjChartRingEquiv_symm_coordinate (b i : Bool) :
    (lineGrassmannianProjChartRingEquiv K b).symm (chartCoordinate I₀ b i) =
      if i = b then 1 else MvPolynomial.X (0, 0) := by
  by_cases h : i = b
  · subst i
    rw [chartCoordinate_self, map_one, if_pos rfl]
  · have hi : i = !b := by cases b <;> cases i <;> simp_all
    rw [if_neg h, hi]
    exact (congrArg (lineGrassmannianProjChartRingEquiv K b).symm
      (lineGrassmannianProjChartRingEquiv_X K b (0, 0)).symm).trans
        ((lineGrassmannianProjChartRingEquiv K b).symm_apply_apply _)

lemma lineGrassmannianProjChartIso_functions (b : Bool) (f : X ⟶ Spec (.of (ChartRing I₀ b))) :
    grassmannianChartFunctions K (f ≫ (lineGrassmannianProjChartIso K b).hom) =
      lineChartMatrix Γ(X, ⊤) (affineFunctionHom f (chartCoordinate I₀ b (!b))) := by
  funext i j
  exact (RingHom.congr_fun (affineFunctionHom_comp_Spec f
    (lineGrassmannianProjChartRingEquiv K b).toRingHom) (MvPolynomial.X (i, j))).trans
      (congrArg (affineFunctionHom f) (lineGrassmannianProjChartRingEquiv_X K b (i, j)))

lemma lineGrassmannianProjChartIso_inv_coordinate (b i : Bool)
    (f : X ⟶ grassmannianChartScheme K 1 1) :
    affineFunctionHom (f ≫ (lineGrassmannianProjChartIso K b).inv) (chartCoordinate I₀ b i) =
      if i = b then 1 else grassmannianChartFunctions K f 0 0 := by
  have he := RingHom.congr_fun (affineFunctionHom_comp_Spec f
    (lineGrassmannianProjChartRingEquiv K b).symm.toRingHom) (chartCoordinate I₀ b i)
  exact he.trans (by
    change affineFunctionHom f ((lineGrassmannianProjChartRingEquiv K b).symm (chartCoordinate I₀ b i)) = _
    rw [lineGrassmannianProjChartRingEquiv_symm_coordinate]
    split_ifs
    · exact map_one (affineFunctionHom f)
    · rfl)

lemma lineGrassmannianProjChartIso_inv_base (b : Bool)
    (f : X ⟶ grassmannianChartScheme K 1 1) :
    (affineFunctionHom (f ≫ (lineGrassmannianProjChartIso K b).inv)).comp (chartBaseMap I₀ b) =
      (affineFunctionHom f).comp MvPolynomial.C := by
  apply RingHom.ext
  intro k
  exact (RingHom.congr_fun (affineFunctionHom_comp_Spec f
    (lineGrassmannianProjChartRingEquiv K b).symm.toRingHom) (chartBaseMap I₀ b k)).trans
      (congrArg (affineFunctionHom f) (lineGrassmannianProjChartRingEquiv_symm_base K b k))

/-- On the actual intersection of two standard projective-line charts, every
normalized homogeneous coordinate on the left is the corresponding
coordinate on the right times the inverse overlap unit.  The statement is
made after pullback to an arbitrary scheme, which is the form used for the
product charts of the Serre pencil. -/
theorem lineProjChartCoordinate_overlap_relation (b c m : Bool)
    (f : X ⟶ Spec (.of (ChartRing I₀ b)))
    (g : X ⟶ Spec (.of (ChartRing I₀ c)))
    (h : f ≫ chartι I₀ b = g ≫ chartι I₀ c) :
    affineFunctionHom f (chartCoordinate I₀ b m) =
      affineFunctionHom
          ((isPullback_chartOverlap I₀ b c).lift f g h)
          (↑((chartOverlapUnit I₀ b c)⁻¹)) *
        affineFunctionHom g (chartCoordinate I₀ c m) := by
  let H := isPullback_chartOverlap I₀ b c
  let a := H.lift f g h
  have ha := H.lift_fst f g h
  have hb := H.lift_snd f g h
  calc
    affineFunctionHom f (chartCoordinate I₀ b m) =
        affineFunctionHom a (chartOverlapLeftMap I₀ b c
          (chartCoordinate I₀ b m)) := by
      exact (congrArg (fun q => affineFunctionHom q (chartCoordinate I₀ b m))
        ha.symm).trans
          (RingHom.congr_fun
            (affineFunctionHom_comp_Spec a (chartOverlapLeftMap I₀ b c))
            (chartCoordinate I₀ b m))
    _ = affineFunctionHom a
          (↑((chartOverlapUnit I₀ b c)⁻¹) *
            chartOverlapRightMap I₀ b c (chartCoordinate I₀ c m)) := by
      rw [chartOverlap_coordinate_relation]
    _ = affineFunctionHom a (↑((chartOverlapUnit I₀ b c)⁻¹)) *
          affineFunctionHom a
            (chartOverlapRightMap I₀ b c (chartCoordinate I₀ c m)) := by
      rw [map_mul]
    _ = affineFunctionHom a (↑((chartOverlapUnit I₀ b c)⁻¹)) *
          affineFunctionHom g (chartCoordinate I₀ c m) := by
      congr 1
      exact (RingHom.congr_fun
        (affineFunctionHom_comp_Spec a (chartOverlapRightMap I₀ b c))
        (chartCoordinate I₀ c m)).symm.trans
          (congrArg (fun q => affineFunctionHom q (chartCoordinate I₀ c m)) hb)

/-- The actual Proj overlap defines the same graph submodule in both projective-line charts. -/
theorem lineProjChartFunctions_submodule_eq (b c : Bool)
    (f : X ⟶ Spec (.of (ChartRing I₀ b))) (g : X ⟶ Spec (.of (ChartRing I₀ c)))
    (h : f ≫ chartι I₀ b = g ≫ chartι I₀ c) :
    grassmannianChartSubmodule Γ(X, ⊤) (lineChartPermutation b)
        (lineChartMatrix Γ(X, ⊤) (affineFunctionHom f (chartCoordinate I₀ b (!b)))) =
      grassmannianChartSubmodule Γ(X, ⊤) (lineChartPermutation c)
        (lineChartMatrix Γ(X, ⊤) (affineFunctionHom g (chartCoordinate I₀ c (!c)))) := by
  apply (lineGrassmannianChartSubmodule_eq_iff Γ(X, ⊤) b c _ _).mpr
  by_cases hbc : b = c
  · subst c
    rw [if_pos rfl]
    have hfg : f = g := (cancel_mono (chartι I₀ b)).mp h
    rw [hfg]
  · rw [if_neg hbc]
    have hnb : (!b) = c := by cases b <;> cases c <;> simp_all
    have hnc : (!c) = b := by cases b <;> cases c <;> simp_all
    let H := isPullback_chartOverlap I₀ b c
    let a := H.lift f g h
    have ha := H.lift_fst f g h
    have hb := H.lift_snd f g h
    have hl : affineFunctionHom f (chartCoordinate I₀ b c) =
        affineFunctionHom a (↑((chartOverlapUnit I₀ b c)⁻¹)) := by
      exact (congrArg (fun q => affineFunctionHom q (chartCoordinate I₀ b c)) ha.symm).trans
        ((RingHom.congr_fun (affineFunctionHom_comp_Spec a (chartOverlapLeftMap I₀ b c))
          (chartCoordinate I₀ b c)).trans
            (congrArg (affineFunctionHom a) (chartOverlapUnit_inv I₀ b c).symm))
    have hr : affineFunctionHom g (chartCoordinate I₀ c b) =
        affineFunctionHom a (↑(chartOverlapUnit I₀ b c)) := by
      exact (congrArg (fun q => affineFunctionHom q (chartCoordinate I₀ c b)) hb.symm).trans
        ((RingHom.congr_fun (affineFunctionHom_comp_Spec a (chartOverlapRightMap I₀ b c))
          (chartCoordinate I₀ c b)).trans
            (congrArg (affineFunctionHom a) (chartOverlapUnit_val I₀ b c).symm))
    rw [hnb, hnc, hl, hr, ← map_mul, Units.inv_mul, map_one]

end
end PfaffianDescent
