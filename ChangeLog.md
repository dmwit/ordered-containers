# Revision history for ordered-containers

## 0.2.4 -- 2024-05-18

* Misc. housekeeping -- version bumps, documentation fixes, etc. (thank you Ryan Scott and Andrew Kent!)
* Add `IsList` and `Hashable` instances (thank you Alexis King!)
* the strict variant of `alter`

## 0.2.3 -- 2022-11-01

* `alter` (thank you Raoul Hidalgo Charman!)

## 0.2.2 -- 2019-07-05

* Add `toMap` and `toSet`, which support efficient conversions from
  `OMap`s/`OSet`s to `Map`s/`Set`s, respectively.

## 0.2.1 -- 2019-03-25

* Compatibility fixes from Ryan Scott (thanks!)

## 0.2 -- 2019-03-24

* Support many more operations:
	* Semigroup,Monoid,Data,Typeable for OSet
	* Semigroup,Monoid,Functor,Traversable,Data,Typeable for OMap
	* union and intersection primitives for both
* Document asymptotics (when they vary from Set and Map)

## 0.1.1 -- 2018-10-31

* Metadata changes only

## 0.1.0 -- 2016-12-26

* Documentation fix
* Live up to the package version boundary claims
* Use enough version parts to conform to the PVP

## 0.0 -- 2016-12-23

* First version released on an unsuspecting world
