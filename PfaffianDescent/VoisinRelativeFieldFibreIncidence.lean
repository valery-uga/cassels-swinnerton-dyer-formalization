import PfaffianDescent.VoisinRelativeUniversalDivisor
import PfaffianDescent.ParameterizedIncidenceFibreProduct

/-!
# A field fibre of the relative cubic-surface incidence

The relative zero locus over an equation parameter is identified with the
intersection of the actual surface fibre and the corresponding universal
equation fibre inside ambient projective space times the field point.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K]
  (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
  {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
  (h : E ⟶ projectiveParameters K (Fin 4) 3)
  {S : Type u} [CommRing S] (s : Spec (.of S) ⟶ E)

/-- Taking an equation-parameter field fibre of the fixed-surface zero locus
is equivalent to intersecting the surface fibre with the universal equation
fibre over the same field point. -/
noncomputable def fixedCubicSurfaceEquationZeroLocusFieldIncidenceIso :
    pullback (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≅
      pullback
        (prod.lift
          (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
            pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
          (pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s))
        (prod.lift
          (pullback.fst (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) ≫
            projectiveUniversalToAmbient K (Fin 4) 3)
          (pullback.snd (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h))) := by
  let X := pullback (pullback.snd (hypersurfaceToBase a ha) k) s
  let xA : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    pullback.fst _ _ ≫ pullback.fst (hypersurfaceToBase a ha) k ≫
      hypersurfaceToAmbient a ha
  let xT : X ⟶ Spec (.of S) := pullback.snd _ _
  let uA := projectiveUniversalToAmbient K (Fin 4) 3
  let uP := projectiveUniversalToBase K (Fin 4) 3
  have hm : pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
      fixedCubicSurfaceEquationIncidenceMap a ha k h =
      prod.lift xA (xT ≫ s ≫ h) := by
    change pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
      prod.lift
        (pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
        (pullback.snd (hypersurfaceToBase a ha) k ≫ h) =
      prod.lift xA (xT ≫ s ≫ h)
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, xA]
    · simp only [Category.assoc, prod.lift_snd, xT]
      simpa only [Category.assoc] using
        (congrArg (· ≫ h)
          (pullback.condition : pullback.fst
            (pullback.snd (hypersurfaceToBase a ha) k) s ≫
              pullback.snd (hypersurfaceToBase a ha) k =
            pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s ≫ s))
  exact fixedCubicSurfaceEquationZeroLocusFibreIso a ha k h s ≪≫
    pullback.congrHom hm rfl ≪≫
      parameterizedIncidenceFibreProductIso xA xT uA uP (s ≫ h)

/-- The incidence-fibre comparison preserves the chosen coefficient-ring
point of the relative family. -/
theorem fixedCubicSurfaceEquationZeroLocusFieldIncidenceIso_toBase :
    (fixedCubicSurfaceEquationZeroLocusFieldIncidenceIso a ha k h s).hom ≫
      pullback.fst
        (prod.lift
          (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
            pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
          (pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s))
        (prod.lift
          (pullback.fst (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) ≫
            projectiveUniversalToAmbient K (Fin 4) 3)
          (pullback.snd (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h))) ≫
            pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s =
      pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s := by
  let X := pullback (pullback.snd (hypersurfaceToBase a ha) k) s
  let xA : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    pullback.fst _ _ ≫ pullback.fst (hypersurfaceToBase a ha) k ≫
      hypersurfaceToAmbient a ha
  let xT : X ⟶ Spec (.of S) := pullback.snd _ _
  let uA := projectiveUniversalToAmbient K (Fin 4) 3
  let uP := projectiveUniversalToBase K (Fin 4) 3
  let z := s ≫ h
  let m := pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
    fixedCubicSurfaceEquationIncidenceMap a ha k h
  have hm : m = prod.lift xA (xT ≫ z) := by
    change pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
      prod.lift
        (pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
        (pullback.snd (hypersurfaceToBase a ha) k ≫ h) =
      prod.lift xA (xT ≫ z)
    apply prod.hom_ext
    · simp only [xA, Category.assoc, prod.lift_fst]
    · simp only [xT, z, Category.assoc, prod.lift_snd]
      simpa only [Category.assoc] using
        (congrArg (· ≫ h)
          (pullback.condition : pullback.fst
            (pullback.snd (hypersurfaceToBase a ha) k) s ≫
              pullback.snd (hypersurfaceToBase a ha) k =
            pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s ≫ s))
  let e₀ := fixedCubicSurfaceEquationZeroLocusFibreIso a ha k h s
  let e₁ : pullback m (projectiveUniversalIncidence K (Fin 4) 3) ≅
      pullback (prod.lift xA (xT ≫ z)) (prod.lift uA uP) :=
    pullback.congrHom hm (by rfl)
  let e₂ := parameterizedIncidenceFibreProductIso xA xT uA uP z
  have h₂ : e₂.hom ≫ pullback.fst (prod.lift xA xT)
      (prod.lift (pullback.fst uP z ≫ uA) (pullback.snd uP z)) =
      pullback.fst (prod.lift xA (xT ≫ z)) (prod.lift uA uP) :=
    parameterizedIncidenceFibreProductIso_hom_fst xA xT uA uP z
  have h₁ : e₁.hom ≫ pullback.fst (prod.lift xA (xT ≫ z)) (prod.lift uA uP) =
      pullback.fst m (projectiveUniversalIncidence K (Fin 4) 3) := by
    simp only [e₁, pullback.congrHom, asIso_hom, pullback.map,
      pullback.lift_fst, Category.comp_id]
  change ((e₀ ≪≫ e₁ ≪≫ e₂).hom ≫ pullback.fst (prod.lift xA xT)
    (prod.lift (pullback.fst uP z ≫ uA) (pullback.snd uP z))) ≫ xT = _
  calc
    _ = e₀.hom ≫ e₁.hom ≫
        pullback.fst (prod.lift xA (xT ≫ z)) (prod.lift uA uP) ≫ xT := by
          simpa only [Iso.trans_hom, Category.assoc] using
            congrArg (fun t => e₀.hom ≫ e₁.hom ≫ t ≫ xT) h₂
    _ = e₀.hom ≫ pullback.fst m
        (projectiveUniversalIncidence K (Fin 4) 3) ≫ xT := by
          simpa only [Category.assoc] using
            congrArg (fun t => e₀.hom ≫ t ≫ xT) h₁
    _ = _ := fixedCubicSurfaceEquationZeroLocusFibreIso_toBaseChange a ha k h s

/-- The incidence-fibre comparison also preserves the point of the fixed
surface family, not just the coefficient-ring point. -/
theorem fixedCubicSurfaceEquationZeroLocusFieldIncidenceIso_toSurface :
    (fixedCubicSurfaceEquationZeroLocusFieldIncidenceIso a ha k h s).hom ≫
      pullback.fst
        (prod.lift
          (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
            pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
          (pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s))
        (prod.lift
          (pullback.fst (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) ≫
            projectiveUniversalToAmbient K (Fin 4) 3)
          (pullback.snd (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h))) ≫
      pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s =
    pullback.fst (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≫
      fixedCubicSurfaceEquationZeroLocusToSurface a ha k h := by
  let X := pullback (pullback.snd (hypersurfaceToBase a ha) k) s
  let xA : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    pullback.fst _ _ ≫ pullback.fst (hypersurfaceToBase a ha) k ≫
      hypersurfaceToAmbient a ha
  let xT : X ⟶ Spec (.of S) := pullback.snd _ _
  let uA := projectiveUniversalToAmbient K (Fin 4) 3
  let uP := projectiveUniversalToBase K (Fin 4) 3
  let z := s ≫ h
  let m := pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
    fixedCubicSurfaceEquationIncidenceMap a ha k h
  have hm : m = prod.lift xA (xT ≫ z) := by
    change pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
      prod.lift
        (pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
        (pullback.snd (hypersurfaceToBase a ha) k ≫ h) =
      prod.lift xA (xT ≫ z)
    apply prod.hom_ext
    · simp only [xA, Category.assoc, prod.lift_fst]
    · simp only [xT, z, Category.assoc, prod.lift_snd]
      simpa only [Category.assoc] using
        (congrArg (· ≫ h)
          (pullback.condition : pullback.fst
            (pullback.snd (hypersurfaceToBase a ha) k) s ≫
              pullback.snd (hypersurfaceToBase a ha) k =
            pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s ≫ s))
  let e₀ := fixedCubicSurfaceEquationZeroLocusFibreIso a ha k h s
  let e₁ : pullback m (projectiveUniversalIncidence K (Fin 4) 3) ≅
      pullback (prod.lift xA (xT ≫ z)) (prod.lift uA uP) :=
    pullback.congrHom hm (by rfl)
  let e₂ := parameterizedIncidenceFibreProductIso xA xT uA uP z
  have h₂ : e₂.hom ≫ pullback.fst (prod.lift xA xT)
      (prod.lift (pullback.fst uP z ≫ uA) (pullback.snd uP z)) =
      pullback.fst (prod.lift xA (xT ≫ z)) (prod.lift uA uP) :=
    parameterizedIncidenceFibreProductIso_hom_fst xA xT uA uP z
  have h₁ : e₁.hom ≫ pullback.fst (prod.lift xA (xT ≫ z)) (prod.lift uA uP) =
      pullback.fst m (projectiveUniversalIncidence K (Fin 4) 3) := by
    simp only [e₁, pullback.congrHom, asIso_hom, pullback.map,
      pullback.lift_fst, Category.comp_id]
  change ((e₀ ≪≫ e₁ ≪≫ e₂).hom ≫ pullback.fst (prod.lift xA xT)
    (prod.lift (pullback.fst uP z ≫ uA) (pullback.snd uP z))) ≫
      pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s = _
  calc
    _ = e₀.hom ≫ e₁.hom ≫
        pullback.fst (prod.lift xA (xT ≫ z)) (prod.lift uA uP) ≫
          pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s := by
            simpa only [Iso.trans_hom, Category.assoc] using
              congrArg (fun t => e₀.hom ≫ e₁.hom ≫ t ≫
                pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s) h₂
    _ = e₀.hom ≫ pullback.fst m (projectiveUniversalIncidence K (Fin 4) 3) ≫
          pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s := by
            simpa only [Category.assoc] using
              congrArg (fun t => e₀.hom ≫ t ≫
                pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s) h₁
    _ = _ := by
      simpa only [e₀, m] using
        (fixedCubicSurfaceEquationZeroLocusFibreIso_toSurface a ha k h s)

end PfaffianDescent
