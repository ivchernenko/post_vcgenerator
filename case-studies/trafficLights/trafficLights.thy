theory trafficLights
imports Main
begin

type_synonym variable = nat

type_synonym process = nat

type_synonym pstate = nat

abbreviation requestButton :: variable where
 "requestButton \<equiv> 1"
abbreviation trafficLight:: variable where
"trafficLight \<equiv> 2"
abbreviation requestButtonPressed:: variable where
"requestButtonPressed \<equiv> 3"
definition stop:: "pstate" where "stop \<equiv> 0"
abbreviation minimalRed:: pstate where
"minimalRed \<equiv> 2"
abbreviation redAfterMinimalRed:: pstate where
"redAfterMinimalRed \<equiv> 3"
abbreviation redToGreen:: pstate where
"redToGreen \<equiv> 4"
abbreviation green:: pstate where
"green \<equiv> 5"
abbreviation GREEN:: bool where "GREEN \<equiv>True"
abbreviation RED:: bool where "RED \<equiv> False"
abbreviation PRESSED:: bool where "PRESSED \<equiv> True"
abbreviation NOT_PRESSED:: bool where "NOT_PRESSED \<equiv> False"
abbreviation MINIMAL_RED_TIME_LIMIT:: nat where
"MINIMAL_RED_TIME_LIMIT \<equiv> 100"
abbreviation RED_TO_GREEN_TIME_LIMIT where
"RED_TO_GREEN_TIME_LIMIT \<equiv> 50"
abbreviation GREEN_TIME_LIMIT where
"GREEN_TIME_LIMIT \<equiv> 30"
abbreviation Ctrl:: process where "Ctrl \<equiv> 1"

datatype state = 
  emptyState | 
  toEnv state |
toCon state |
 setVarBool state variable bool  |
  setVarInt state variable int |
setVarAny state bool |
  setPstate state process pstate |
  reset state process

fun getVarBool:: "state \<Rightarrow> variable \<Rightarrow> bool" where
"getVarBool emptyState _ = False" |
"getVarBool (toEnv s) x = getVarBool s x" |
"getVarBool (toCon s) x = getVarBool s x" |
"getVarBool (setVarBool s y v) x =
 (if x=y then v else (getVarBool s x))" |
"getVarBool (setVarInt s _ _) x = getVarBool s x" |
"getVarBool (setVarAny s requestButtonValue) x =
(if x=requestButton then requestButtonValue else
 (getVarBool s x))" |
"getVarBool (setPstate s _ _) x = getVarBool s x" |
"getVarBool (reset s _) x = getVarBool s x" 

fun getVarInt:: "state \<Rightarrow> variable \<Rightarrow> int" where
"getVarInt emptyState _ = 0" |
"getVarInt (toEnv s) x = getVarInt s x" |
"getVarInt (toCon s) x = getVarInt s x" |
"getVarInt (setVarBool s y v) x =
getVarInt s x" |
"getVarInt (setVarInt s y v) x = 
(if x=y then v else (getVarInt s x))" |
"getVarInt (setVarAny s requestButtonValue) x =
getVarInt s x" |
"getVarInt (setPstate s _ _) x = getVarInt s x" |
"getVarInt (reset s _) x = getVarInt s x" 

fun getPstate:: "state \<Rightarrow> process \<Rightarrow> pstate" where
"getPstate emptyState _ = 0" |
"getPstate (toEnv s) p = getPstate s p" |
"getPstate (toCon s) p = getPstate s p" |
"getPstate (setVarBool s _ _) p = getPstate s p" |
"getPstate (setVarInt s _ _) p = getPstate s p" |
"getPstate (setVarAny s _) p = getPstate s p" |
"getPstate (setPstate s p1 q) p =
(if p=p1 then q else (getPstate s p))" |
"getPstate (reset s _) p = getPstate s p"

fun substate:: "state \<Rightarrow> state \<Rightarrow> bool" where
"substate s emptyState =
 (if s = emptyState then True else False)" |
"substate s (toEnv s1) =
 (if s = toEnv s1 then True else substate s s1)" |
"substate s (toCon s1) = 
(if s = toCon s1 then True else substate s s1)" |
"substate s (setVarBool s1 v u) = 
(if s = setVarBool s1 v u then True else 
substate s s1)" |
"substate s (setVarInt s1 v u) =
(if s = setVarInt s1 v u then True else 
substate s s1)" |
"substate s (setVarAny s1 requestButton_value) =
(if s = setVarAny s1 requestButton_value then True else
substate s s1)" |
"substate s (setPstate s1 p q) =
(if s = setPstate s1 p q then True else
substate s s1)" |
"substate s (reset s1 p) =
(if s = reset s1 p then True else
substate s s1)"

fun toEnvNum:: "state \<Rightarrow>state \<Rightarrow> nat" where 
"toEnvNum s emptyState = 0" |
"toEnvNum s (toEnv s1) = 
(if s = toEnv s1 then 0 else toEnvNum s s1 + 1)" |
"toEnvNum s (toCon s1) =
(if s = toCon s1 then 0 else toEnvNum s s1)" |
"toEnvNum s (setVarBool s1 v u) =
(if s = setVarBool s1 v u then 0 else 
toEnvNum s s1)" |
"toEnvNum s (setVarInt s1 v u) =
(if s = setVarInt s1 v u then 0 else
toEnvNum s s1)" |
"toEnvNum s (setVarAny s1 requestButton_value) =
(if s = setVarAny s1 requestButton_value then 0 else
toEnvNum s s1)" |
"toEnvNum s (setPstate s1 p q) =
(if s = setPstate s1 p q then 0 else
toEnvNum s s1)" |
"toEnvNum s (reset s1 p) =
(if s = reset s1 p then 0 else 
toEnvNum s s1)"

fun toConNum:: "state \<Rightarrow>state \<Rightarrow> nat" where 
"toConNum s s1 = (if s=s1 then 0 else (case s1 of
emptyState \<Rightarrow> 0 |
toCon s2 \<Rightarrow> (toConNum s1 s2) + 1 |
toEnv s2 \<Rightarrow> toConNum s1 s2 |
setVarBool s2 _ _ \<Rightarrow> toConNum s1 s2 |
setVarInt s2 _ _ \<Rightarrow> toConNum s1 s2 |
setVarAny s2 _ \<Rightarrow> toConNum s1 s2 |
setPstate s2 _ _ \<Rightarrow> toConNum s1 s2 |
reset s2 _ \<Rightarrow> toConNum s1 s2))"

fun toEnvP::"state \<Rightarrow> bool" where
"toEnvP (toEnv _) = True" |
"toEnvP _ = False"

fun toConP:: "state \<Rightarrow> bool" where
"toConP (toCon _) = True" |
"toConP _ = False"

fun ltimeEnv:: "state \<Rightarrow> process \<Rightarrow> nat" where 
"ltimeEnv emptyState _ = 0" |
"ltimeEnv (toEnv s) p = (ltimeEnv s p) + 1" |
"ltimeEnv (toCon s) p = ltimeEnv s p" |
"ltimeEnv (setVarBool s _ _) p = ltimeEnv s p" |
"ltimeEnv (setVarInt s _ _) p = ltimeEnv s p" |
"ltimeEnv (setVarAny s _) p = ltimeEnv s p" |
"ltimeEnv (setPstate s p1 _) p =
(if p=p1 then 0 else ltimeEnv s p)" |
"ltimeEnv (reset s p1) p =
(if p=p1 then 0 else ltimeEnv s p)"

fun ltimeCon:: "state \<Rightarrow> process \<Rightarrow> nat" where 
"ltimeCon emptyState _ = 0" |
"ltimeCon (toCon s) p = (ltimeCon s p) + 1" |
"ltimeCon (toEnv s) p = ltimeCon s p" |
"ltimeCon (setVarBool s _ _) p = ltimeCon s p" |
"ltimeCon (setVarInt s _ _) p = ltimeCon s p" |
"ltimeCon (setVarAny s _) p = ltimeCon s p" |
"ltimeCon (setPstate s p1 _) p =
(if p=p1 then 0 else ltimeCon s p)" |
"ltimeCon (reset s p1) p =
(if p=p1 then 0 else ltimeCon s p)"

fun predEnv:: "state \<Rightarrow> state" where
"predEnv emptyState = emptyState" |
"predEnv (toEnv s) =
(if (toEnvP s) then s else predEnv s)" |
"predEnv (toCon s) =
 (if (toEnvP s) then s else predEnv s)" |
"predEnv (setVarBool s _ _) = 
(if (toEnvP s) then s else predEnv s)" |
"predEnv (setVarInt s _ _) = 
(if (toEnvP s) then s else predEnv s)" |
"predEnv (setVarAny s _ ) = 
(if (toEnvP s) then s else predEnv s)" |
"predEnv (setPstate s _ _) = 
(if (toEnvP s) then s else predEnv s)" |
"predEnv (reset s _) = 
(if (toEnvP s) then s else predEnv s)"

fun predCon:: "state \<Rightarrow> state" where
"predCon emptyState = emptyState" |
"predCon (toCon s) =
(case s of toCon _ \<Rightarrow> s | _ \<Rightarrow> predCon s)" |
"predCon (toEnv s) =
 (case s of toCon _ \<Rightarrow> s | _ \<Rightarrow> predCon s)" |
"predCon (setVarBool s _ _) = 
(case s of toCon _ \<Rightarrow> s | _ \<Rightarrow> predCon s)" |
"predCon (setVarInt s _ _) = 
(case s of toCon _ \<Rightarrow> s | _ \<Rightarrow> predCon s)" |
"predCon (setVarAny s _ ) = 
(case s of toCon _ \<Rightarrow> s | _ \<Rightarrow> predCon s)" |
"predCon (setPstate s _ _) = 
(case s of toCon _ \<Rightarrow> s | _ \<Rightarrow> predCon s)" |
"predCon (reset s _) = 
(case s of toCon _  \<Rightarrow> s | _ \<Rightarrow> predCon s)"

fun shiftEnv:: "state \<Rightarrow> nat \<Rightarrow> state" where
"shiftEnv s 0 = s" |
"shiftEnv s (Suc n) = predEnv (shiftEnv s n)"

fun shiftCon:: "state \<Rightarrow> nat \<Rightarrow> state" where
"shiftCon s 0 = s" |
"shiftCon s (Suc n) = predCon (shiftCon s n)"

definition env:: "state => bool \<Rightarrow> bool" where
"env s requestButton_value \<equiv> True"

(*Verification Conditions*)

definition VC1 where
"VC1 inv0 s0 \<equiv>
s0 = toEnv (setPstate emptyState Ctrl minimalRed) \<longrightarrow>
inv0 s0"

definition VC2 where
"VC2 inv0 s0 requestButton_value \<equiv>
inv0 s0 \<and>
env (setVarAny s0 requestButton_value) 
requestButton_value \<and>
getPstate  (setVarAny s0 requestButton_value)
 Ctrl = minimalRed \<and>
getVarBool  (setVarAny s0 requestButton_value)
 requestButton \<and>
100 \<le> ltimeEnv 
(setVarBool 
 (setVarAny s0  requestButton_value)
 requestButtonPressed
 True)
 Ctrl \<longrightarrow>
inv0 (toEnv 
(setPstate 
(setVarBool
 (setVarAny s0  requestButton_value)
 requestButtonPressed 
True)
 Ctrl
 redAfterMinimalRed))"

definition VC3 where
"VC3 inv0 s0 requestButton_value \<equiv>
inv0 s0 \<and>
env (setVarAny s0 requestButton_value) 
requestButton_value \<and>
getPstate  (setVarAny s0 requestButton_value)
 Ctrl = minimalRed \<and>
getVarBool  (setVarAny s0 requestButton_value)
 requestButton \<and>
\<not> 100 \<le> ltimeEnv 
(setVarBool 
 (setVarAny s0  requestButton_value)
 requestButtonPressed
 True)
 Ctrl \<longrightarrow>
inv0 (toEnv 
(setVarBool
 (setVarAny s0  requestButton_value)
 requestButtonPressed 
True))"

definition VC4 where
"VC4 inv0 s0 requestButton_value \<equiv>
inv0 s0 \<and>
env (setVarAny s0 requestButton_value) 
requestButton_value \<and>
getPstate  (setVarAny s0 requestButton_value)
 Ctrl = minimalRed \<and>
\<not> getVarBool  (setVarAny s0 requestButton_value)
 requestButton \<and>
100 \<le> ltimeEnv  
 (setVarAny s0  requestButton_value)
 Ctrl \<longrightarrow>
inv0 (toEnv 
(setPstate 
 (setVarAny s0  requestButton_value)
 Ctrl
 redAfterMinimalRed))"

definition VC5 where
"VC5 inv0 s0 requestButton_value \<equiv>
inv0 s0 \<and>
env (setVarAny s0 requestButton_value) 
requestButton_value \<and>
getPstate  (setVarAny s0 requestButton_value)
 Ctrl = minimalRed \<and>
\<not> getVarBool  (setVarAny s0 requestButton_value)
 requestButton \<and>
\<not> 100 \<le> ltimeEnv 
 (setVarAny s0  requestButton_value)
 Ctrl \<longrightarrow>
inv0 (toEnv 
 (setVarAny s0  requestButton_value)
)"

definition VC6 where
"VC6 inv0 s0 requestButton_value \<equiv>
inv0 s0 \<and>
env (setVarAny s0 requestButton_value) 
requestButton_value \<and>
getPstate  (setVarAny s0 requestButton_value)
 Ctrl = redAfterMinimalRed \<and>
(getVarBool (setVarAny s0 requestButton_value) 
requestButtonPressed \<or> 
getVarBool (setVarAny s0 requestButton_value) 
requestButton) \<longrightarrow>
inv0 (toEnv (setPstate
 (setVarAny s0 requestButton_value)
 Ctrl
 redToGreen))"

definition VC7 where
"VC7 inv0 s0 requestButton_value \<equiv>
inv0 s0 \<and>
env (setVarAny s0 requestButton_value) 
requestButton_value \<and>
getPstate  (setVarAny s0 requestButton_value)
 Ctrl = redAfterMinimalRed \<and>
\<not> (getVarBool (setVarAny s0 requestButton_value) 
requestButtonPressed \<or> 
getVarBool (setVarAny s0 requestButton_value) 
requestButton) \<longrightarrow>
inv0 (toEnv (setVarAny s0 requestButton_value))"

definition VC8 where
"VC8 inv0 s0 requestButton_value \<equiv>
inv0 s0 \<and>
env (setVarAny s0 requestButton_value) 
requestButton_value \<and>
getPstate  (setVarAny s0 requestButton_value)
 Ctrl = redToGreen \<and>
50 \<le> 
ltimeEnv (setVarAny s0 requestButton_value) Ctrl \<longrightarrow>
inv0 (toEnv (setPstate (setVarBool (setVarBool
(setVarAny s0 requestButton_value)
trafficLight
GREEN)
requestButtonPressed
False)
Ctrl
green))"

definition VC9 where
"VC9 inv0 s0 requestButton_value \<equiv>
inv0 s0 \<and>
env (setVarAny s0 requestButton_value) 
requestButton_value \<and>
getPstate  (setVarAny s0 requestButton_value)
 Ctrl = redToGreen \<and>
\<not> 50 \<le> 
ltimeEnv (setVarAny s0 requestButton_value) Ctrl \<longrightarrow>
inv0 (toEnv (setVarAny s0 requestButton_value))"

definition VC10 where
"VC10 inv0 s0 requestButton_value \<equiv>
inv0 s0 \<and>
env (setVarAny s0 requestButton_value) 
requestButton_value \<and>
getPstate  (setVarAny s0 requestButton_value)
 Ctrl = green \<and>
300 \<le> 
ltimeEnv (setVarAny s0 requestButton_value) Ctrl \<longrightarrow>
inv0 (toEnv (setPstate (setVarBool
(setVarAny s0 requestButton_value)
trafficLight
RED)
Ctrl
minimalRed))"

definition VC11 where
"VC11 inv0 s0 requestButton_value \<equiv>
inv0 s0 \<and>
env (setVarAny s0 requestButton_value) 
requestButton_value \<and>
getPstate  (setVarAny s0 requestButton_value)
 Ctrl = green \<and>
\<not> 300 \<le> 
ltimeEnv (setVarAny s0 requestButton_value) Ctrl \<longrightarrow>
inv0 (toEnv (setVarAny s0 requestButton_value))"

end