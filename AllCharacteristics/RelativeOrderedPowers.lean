import AllCharacteristics.RelativeFamilyFunctor
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Ordered powers of a family

Iterated fiber products construct the actual scheme of ordered tuples on a
family. The construction retains its morphism to the base and its coordinate
projections. Properness and smoothness follow by base change and composition.
These schemes are the ambient spaces for the distinct-point configuration
loci used in the relative symmetric-power construction.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The ordered `n`-fold fiber power, as an actual scheme over the base. -/
noncomputable def orderedFamilyPowerOver : ℕ → Over S
  | 0 => Over.mk (𝟙 S)
  | n + 1 => Over.mk (pullback.fst f (orderedFamilyPowerOver n).hom ≫ f)

/-- The first coordinate of the next fiber power. -/
noncomputable def orderedFamilyHead (n : ℕ) :
    orderedFamilyPowerOver f (n + 1) ⟶ Over.mk f :=
  Over.homMk (pullback.fst f (orderedFamilyPowerOver f n).hom) rfl

/-- The remaining ordered tuple, obtained from the other pullback projection. -/
noncomputable def orderedFamilyTail (n : ℕ) :
    orderedFamilyPowerOver f (n + 1) ⟶ orderedFamilyPowerOver f n :=
  Over.homMk (pullback.snd f (orderedFamilyPowerOver f n).hom) pullback.condition.symm

/-- All coordinate projections of the actual relative ordered power. -/
noncomputable def orderedFamilyCoordinate : (n : ℕ) →
    Fin n → (orderedFamilyPowerOver f n ⟶ Over.mk f)
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases (orderedFamilyHead f n)
      (fun j ↦ orderedFamilyTail f n ≫ orderedFamilyCoordinate n j) i

/-- Every coordinate projection lies over exactly the original base morphism. -/
theorem orderedFamilyCoordinate_toBase (n : ℕ) (i : Fin n) :
    (orderedFamilyCoordinate f n i).left ≫ f = (orderedFamilyPowerOver f n).hom :=
  Over.w (orderedFamilyCoordinate f n i)

/-- The actual ordered fiber powers of a proper family remain proper. -/
instance isProper_orderedFamilyPower (n : ℕ) [IsProper f] :
    IsProper (orderedFamilyPowerOver f n).hom := by
  induction n with
  | zero =>
    change IsProper (𝟙 S)
    infer_instance
  | succ n ih =>
    have := ih
    change IsProper (pullback.fst f (orderedFamilyPowerOver f n).hom ≫ f)
    infer_instance

/-- The actual ordered fiber powers of a smooth family remain smooth. -/
instance smooth_orderedFamilyPower (n : ℕ) [Smooth f] :
    Smooth (orderedFamilyPowerOver f n).hom := by
  induction n with
  | zero =>
    change Smooth (𝟙 S)
    infer_instance
  | succ n ih =>
    have := ih
    change Smooth (pullback.fst f (orderedFamilyPowerOver f n).hom ≫ f)
    infer_instance

/-- Relative ordered powers of a locally finite type family over a locally
Noetherian base are locally Noetherian. -/
theorem isLocallyNoetherian_orderedFamilyPower (n : ℕ) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] : IsLocallyNoetherian (orderedFamilyPowerOver f n).left := by
  induction n with
  | zero =>
    change IsLocallyNoetherian S
    infer_instance
  | succ n ih =>
    change IsLocallyNoetherian (pullback f (orderedFamilyPowerOver f n).hom)
    letI : IsLocallyNoetherian (orderedFamilyPowerOver f n).left := ih
    exact inferInstance

/-- An iterated fiber power of a geometrically integral family is integral.
The flatness and universal-openness hypotheses make geometric integrality
stable as an ordinary integrality statement after each base change. -/
theorem isIntegral_orderedFamilyPower_of_geometricallyIntegral (n : ℕ)
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [LocallyOfFiniteType f]
    [IsIntegral S] [IsLocallyNoetherian S] : IsIntegral (orderedFamilyPowerOver f n).left := by
  induction n with
  | zero =>
    change IsIntegral S
    infer_instance
  | succ n ih =>
    change IsIntegral (pullback f (orderedFamilyPowerOver f n).hom)
    letI : IsIntegral (orderedFamilyPowerOver f n).left := ih
    letI : IsLocallyNoetherian (orderedFamilyPowerOver f n).left :=
      isLocallyNoetherian_orderedFamilyPower f n
    exact inferInstance

/-- Two maps to a nonempty ordered power agree when their head and tail agree. -/
theorem orderedFamilyPower_hom_ext {T : Over S} (n : ℕ)
    {a b : T ⟶ orderedFamilyPowerOver f (n + 1)}
    (h₀ : a ≫ orderedFamilyHead f n = b ≫ orderedFamilyHead f n)
    (h₁ : a ≫ orderedFamilyTail f n = b ≫ orderedFamilyTail f n) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun c ↦ c.left) h₀
  · exact congrArg (fun c ↦ c.left) h₁

end AllCharacteristics
