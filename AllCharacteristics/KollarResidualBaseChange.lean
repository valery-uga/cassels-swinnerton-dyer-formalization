import AllCharacteristics.KollarCoefficientFractionMap
import AllCharacteristics.KollarAdjoinRootCoefficientMap
import AllCharacteristics.KollarSmoothGenericResidual

/-! Coefficient base change of the actual generic residual
extension. The direction variables and the chosen residual root are preserved.
For `l = AlgebraicClosure k` the target remains a residual extension over
`Frac(l[U₀,U₁,U₂])`; it is not an unspecified algebraic closure of the old field.
-/

noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry HomogeneousProjective PfaffianDescent MvPolynomial Polynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem kollarBasePoint_map_coefficients
    {k l : Type u} [Field k] [Field l] (f : k →+* l) :
    (fun i => f (kollarBasePoint k i)) = kollarBasePoint l := by
  funext i
  fin_cases i <;> simp [kollarBasePoint]

theorem kollarZeroAffineDirection_map_coefficients
    {k l : Type u} [Field k] [Field l] (f : k →+* l) :
    (fun i => f (kollarAffineLineDirection k (fun _ => 0) i)) =
      kollarAffineLineDirection l (fun _ => 0) := by
  funext i
  fin_cases i <;> simp [kollarAffineLineDirection]

theorem kollarProjectivePolynomialDirection_map_coefficients
    {k l : Type u} [Field k] [Field l] (f : k →+* l) :
    (fun i => (kollarProjectiveLinePolynomialDirection k i).map f) =
      kollarProjectiveLinePolynomialDirection l := by
  rw [kollarProjectiveLinePolynomialDirection_eq_standard,
    kollarProjectiveLinePolynomialDirection_eq_standard]
  funext i
  fin_cases i <;> simp

theorem kollarGenericProjectiveLineDirection_map_coefficients
    {k l : Type u} [Field k] [Field l] (f : k →+* l) :
    (fun i => mvFractionCoefficientMap (Fin 3) f
      (kollarGenericProjectiveLineDirection k i)) =
      kollarGenericProjectiveLineDirection l := by
  funext i
  change mvFractionCoefficientMap (Fin 3) f
      (algebraMap (MvPolynomial (Fin 3) k) (FractionRing (MvPolynomial (Fin 3) k))
        (kollarProjectiveLinePolynomialDirection k i)) = _
  rw [mvFractionCoefficientMap_algebraMap]
  change algebraMap (MvPolynomial (Fin 3) l) (FractionRing (MvPolynomial (Fin 3) l))
      ((kollarProjectiveLinePolynomialDirection k i).map f) = _
  rw [congrFun (kollarProjectivePolynomialDirection_map_coefficients f) i]
  rfl

theorem kollarGenericBasePoint_map_coefficients
    {k l : Type u} [Field k] [Field l] (f : k →+* l) :
    (fun i => mvFractionCoefficientMap (Fin 3) f
      (algebraMap k (FractionRing (MvPolynomial (Fin 3) k)) (kollarBasePoint k i))) =
      fun i => algebraMap l (FractionRing (MvPolynomial (Fin 3) l))
        (kollarBasePoint l i) := by
  funext i
  rw [mvFractionCoefficientMap_base]
  rw [congrFun (kollarBasePoint_map_coefficients f) i]

theorem kollarGenericCubic_map_coefficients
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4) :
    (c.map (algebraMap k (FractionRing (MvPolynomial (Fin 3) k)))).map
        (mvFractionCoefficientMap (Fin 3) f) =
      (c.map f).map (algebraMap l (FractionRing (MvPolynomial (Fin 3) l))) := by
  funext i
  exact mvFractionCoefficientMap_base (Fin 3) f (c i)

/-- Exact coefficient identity for the actual generic residual quadratic. -/
theorem kollarGenericResidualPolynomial_map_coefficients
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4) :
    (kollarGenericResidualPolynomial c).map (mvFractionCoefficientMap (Fin 3) f) =
      kollarGenericResidualPolynomial (c.map f) := by
  have h := Cubic.map_lineResidualPolynomial (mvFractionCoefficientMap (Fin 3) f)
    (c.map (algebraMap k (FractionRing (MvPolynomial (Fin 3) k))))
    (fun i => algebraMap k (FractionRing (MvPolynomial (Fin 3) k)) (kollarBasePoint k i))
    (kollarGenericProjectiveLineDirection k)
  rw [kollarGenericCubic_map_coefficients,
    kollarGenericBasePoint_map_coefficients,
    kollarGenericProjectiveLineDirection_map_coefficients] at h
  exact h

/-- The explicit map of generic residual root extensions. The coefficient
field map keeps the three direction variables independent. -/
def kollarResidualRootBaseChange
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4) :
    AdjoinRoot (kollarGenericResidualPolynomial c) →+*
      AdjoinRoot (kollarGenericResidualPolynomial (c.map f)) :=
  adjoinRootCoefficientMap (mvFractionCoefficientMap (Fin 3) f)
    (kollarGenericResidualPolynomial c) (kollarGenericResidualPolynomial (c.map f))
    (kollarGenericResidualPolynomial_map_coefficients f c)

@[simp] theorem kollarResidualRootBaseChange_root
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4) :
    kollarResidualRootBaseChange f c (AdjoinRoot.root (kollarGenericResidualPolynomial c)) =
      AdjoinRoot.root (kollarGenericResidualPolynomial (c.map f)) := by
  exact adjoinRootCoefficientMap_root _ _ _ _

@[simp] theorem kollarResidualRootBaseChange_of
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4)
    (a : FractionRing (MvPolynomial (Fin 3) k)) :
    kollarResidualRootBaseChange f c (AdjoinRoot.of (kollarGenericResidualPolynomial c) a) =
      AdjoinRoot.of (kollarGenericResidualPolynomial (c.map f))
        (mvFractionCoefficientMap (Fin 3) f a) := by
  exact adjoinRootCoefficientMap_of _ _ _ _ a

@[simp] theorem kollarResidualRootBaseChange_variable
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4) (i : Fin 3) :
    kollarResidualRootBaseChange f c
        (AdjoinRoot.of (kollarGenericResidualPolynomial c)
          (algebraMap (MvPolynomial (Fin 3) k) (FractionRing (MvPolynomial (Fin 3) k))
            (MvPolynomial.X i))) =
      AdjoinRoot.of (kollarGenericResidualPolynomial (c.map f))
        (algebraMap (MvPolynomial (Fin 3) l) (FractionRing (MvPolynomial (Fin 3) l))
          (MvPolynomial.X i)) := by
  rw [kollarResidualRootBaseChange_of, mvFractionCoefficientMap_X]

@[simp] theorem kollarResidualRootBaseChange_base
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4) (a : k) :
    kollarResidualRootBaseChange f c
        (AdjoinRoot.of (kollarGenericResidualPolynomial c)
          (algebraMap k (FractionRing (MvPolynomial (Fin 3) k)) a)) =
      AdjoinRoot.of (kollarGenericResidualPolynomial (c.map f))
        (algebraMap l (FractionRing (MvPolynomial (Fin 3) l)) (f a)) := by
  rw [kollarResidualRootBaseChange_of, mvFractionCoefficientMap_base]

/-- Homogeneity of the original equation passes to the coefficient-extended
cubic tensor's literal polynomial. -/
theorem kollarMappedCubic_isHomogeneous
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3) :
    (c.map f).toMvPolynomial.IsHomogeneous 3 := by
  rw [Cubic.toMvPolynomial_map]
  exact hhom.map f

theorem kollarMappedCubic_smooth
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    Smooth (hypersurfaceToBase (c.map f).toMvPolynomial
      (kollarMappedCubic_isHomogeneous f c hhom)) := by
  exact (smooth_hypersurfaceToBase_congr (c.toMvPolynomial.map f)
    (c.map f).toMvPolynomial (hhom.map f)
    (kollarMappedCubic_isHomogeneous f c hhom) (Cubic.toMvPolynomial_map f c).symm).mp
      (smooth_hypersurfaceToBase_map f c.toMvPolynomial hhom)

theorem kollarMappedCubic_basePoint_eval
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4)
    (hp : c.eval (kollarBasePoint k) = 0) :
    (c.map f).eval (kollarBasePoint l) = 0 := by
  have h := Cubic.eval_map f c (kollarBasePoint k)
  rw [kollarBasePoint_map_coefficients, hp, map_zero] at h
  exact h

theorem kollarMappedCubic_secant_ne_zero
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4)
    (hsec : c.mixed (kollarBasePoint k)
      (kollarAffineLineDirection k (fun _ => 0)) ≠ 0) :
    (c.map f).mixed (kollarBasePoint l)
      (kollarAffineLineDirection l (fun _ => 0)) ≠ 0 := by
  have h := Cubic.mixed_map f c (kollarBasePoint k)
    (kollarAffineLineDirection k (fun _ => 0))
  rw [kollarBasePoint_map_coefficients, kollarZeroAffineDirection_map_coefficients] at h
  rw [h]
  intro hz
  exact hsec (f.injective (by simpa only [map_zero] using hz))

/-- The displayed root-extension map is injective: irreducibility over the
new rational function field is proved from the coefficient-extended smooth
cubic. In particular no algebraic-closure argument for the old root field is
used to assert genericity of the center. -/
theorem kollarResidualRootBaseChange_injective_of_smooth
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hp : c.eval (kollarBasePoint k) = 0)
    (hsec : c.mixed (kollarBasePoint k)
      (kollarAffineLineDirection k (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    Function.Injective (kollarResidualRootBaseChange f c) := by
  letI : Smooth (hypersurfaceToBase (c.map f).toMvPolynomial
      (kollarMappedCubic_isHomogeneous f c hhom)) := kollarMappedCubic_smooth f c hhom
  have hirr := kollarGenericResidualPolynomial_irreducible_of_smooth c hhom hp hsec
  have hirrNew := kollarGenericResidualPolynomial_irreducible_of_smooth
    (c.map f) (kollarMappedCubic_isHomogeneous f c hhom)
    (kollarMappedCubic_basePoint_eval f c hp) (kollarMappedCubic_secant_ne_zero f c hsec)
  exact adjoinRootCoefficientMap_injective _ _ _
    (kollarGenericResidualPolynomial_map_coefficients f c) hirr hirrNew

end AllCharacteristics
