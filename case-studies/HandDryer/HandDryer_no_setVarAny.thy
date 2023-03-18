theory HandDryer_no_setVarAny
imports Main
begin

abbreviation ON :: "bool" where "ON \<equiv> True"
abbreviation OFF :: "bool" where "OFF \<equiv> False"



definition dryer :: "nat" where "dryer \<equiv> Suc (Suc 0)"
definition Ctrl :: "nat" where "Ctrl \<equiv> Suc (Suc (Suc 0))"
definition waiting :: "nat" where "waiting \<equiv> Suc (Suc (Suc (Suc 0)))"
definition drying :: "nat" where "drying \<equiv> Suc (Suc (Suc (Suc (Suc 0))))"

type_synonym variable = nat

type_synonym process = nat

type_synonym pstate = nat

abbreviation hands :: variable where "hands \<equiv> Suc 0"
definition stop:: "pstate" where "stop \<equiv> 0"
datatype state = 
  emptyState | 
  toEnv state |
 setVarBool state variable bool  |
  setVarInt state variable int |
  setPstate state process pstate |
  reset state process

fun getVarBool:: "state \<Rightarrow> variable \<Rightarrow> bool" where
"getVarBool emptyState _ = False" |
"getVarBool (toEnv s) x = getVarBool s x" |
"getVarBool (setVarBool s y v) x =
 (if x=y then v else (getVarBool s x))" |
"getVarBool (setVarInt s _ _) x = getVarBool s x" |
"getVarBool (setPstate s _ _) x = getVarBool s x" |
"getVarBool (reset s _) x = getVarBool s x" 

fun getVarInt:: "state \<Rightarrow> variable \<Rightarrow> int" where
"getVarInt emptyState _ = 0" |
"getVarInt (toEnv s) x = getVarInt s x" |
"getVarInt (setVarBool s y v) x =
getVarInt s x" |
"getVarInt (setVarInt s y v) x = 
(if x=y then v else (getVarInt s x))" |
"getVarInt (setPstate s _ _) x = getVarInt s x" |
"getVarInt (reset s _) x = getVarInt s x" 

fun getPstate:: "state \<Rightarrow> process \<Rightarrow> pstate" where
"getPstate emptyState _ = 0" |
"getPstate (toEnv s) p = getPstate s p" |
"getPstate (setVarBool s _ _) p = getPstate s p" |
"getPstate (setVarInt s _ _) p = getPstate s p" |
"getPstate (setPstate s p1 q) p =
(if p=p1 then q else (getPstate s p))" |
"getPstate (reset s _) p = getPstate s p"

fun substate:: "state \<Rightarrow> state \<Rightarrow> bool" where
"substate s emptyState =
 (if s = emptyState then True else False)" |
"substate s (toEnv s1) =
 (if s = toEnv s1 then True else substate s s1)" |
"substate s (setVarBool s1 v u) = 
(if s = setVarBool s1 v u then True else 
substate s s1)" |
"substate s (setVarInt s1 v u) =
(if s = setVarInt s1 v u then True else 
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
"toEnvNum s (setVarBool s1 v u) =
(if s = setVarBool s1 v u then 0 else 
toEnvNum s s1)" |
"toEnvNum s (setVarInt s1 v u) =
(if s = setVarInt s1 v u then 0 else
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
toEnv s2 \<Rightarrow> toConNum s1 s2 |
setVarBool s2 _ _ \<Rightarrow> toConNum s1 s2 |
setVarInt s2 _ _ \<Rightarrow> toConNum s1 s2 |
setPstate s2 _ _ \<Rightarrow> toConNum s1 s2 |
reset s2 _ \<Rightarrow> toConNum s1 s2))"

fun toEnvP::"state \<Rightarrow> bool" where
"toEnvP (toEnv _) = True" |
"toEnvP _ = False"

fun ltimeEnv:: "state \<Rightarrow> process \<Rightarrow> nat" where 
"ltimeEnv emptyState _ = 0" |
"ltimeEnv (toEnv s) p = (ltimeEnv s p) + 1" |
"ltimeEnv (setVarBool s _ _) p = ltimeEnv s p" |
"ltimeEnv (setVarInt s _ _) p = ltimeEnv s p" |
"ltimeEnv (setPstate s p1 _) p =
(if p=p1 then 0 else ltimeEnv s p)" |
"ltimeEnv (reset s p1) p =
(if p=p1 then 0 else ltimeEnv s p)"

fun predEnv:: "state \<Rightarrow> state" where
"predEnv emptyState = emptyState" |
"predEnv (toEnv s) =
(if (toEnvP s) then s else predEnv s)" |
"predEnv (setVarBool s _ _) = 
(if (toEnvP s) then s else predEnv s)" |
"predEnv (setVarInt s _ _) = 
(if (toEnvP s) then s else predEnv s)" |
"predEnv (setPstate s _ _) = 
(if (toEnvP s) then s else predEnv s)" |
"predEnv (reset s _) = 
(if (toEnvP s) then s else predEnv s)"

fun shiftEnv:: "state \<Rightarrow> nat \<Rightarrow> state" where
"shiftEnv s 0 = s" |
"shiftEnv s (Suc n) = predEnv (shiftEnv s n)"


definition env:: "state \<Rightarrow> bool \<Rightarrow> bool" where
"env s hands_value = True"

definition VC1  where 
" VC1 inv0 s0 \<equiv>
s0 = toEnv (setPstate emptyState Ctrl waiting) \<longrightarrow>
inv0 s0
"

definition VC2 where
"
VC2 inv0 s0 hands_value \<equiv>
(inv0 s0 \<and>
env (setVarBool s0 hands hands_value) hands_value) \<and>
(getPstate (setVarBool s0 hands hands_value) Ctrl = waiting
 \<and> getVarBool (setVarBool s0 hands hands_value) hands = ON)
\<longrightarrow> inv0
(toEnv 
(setPstate 
(setVarBool (setVarBool s0 hands hands_value) dryer ON) 
Ctrl
drying)
)
"

definition VC3 where
"
VC3 inv0 s0 hands_value \<equiv>
(inv0 s0 \<and>
env (setVarBool s0 hands hands_value) hands_value) \<and>
(getPstate (setVarBool s0 hands hands_value) Ctrl = waiting
 \<and> getVarBool (setVarBool s0 hands hands_value) hands \<noteq> ON)
\<longrightarrow> inv0
(toEnv 
(setVarBool (setVarBool s0 hands hands_value) dryer OFF) 
)
"

definition VC4 where
"VC4 inv0 s0 hands_value \<equiv>
(inv0 s0 \<and>
env (setVarBool s0 hands hands_value) hands_value) \<and>
(getPstate (setVarBool s0 hands hands_value) Ctrl = drying
\<and> getVarBool (setVarBool s0 hands hands_value) hands = ON
\<and>
 10 \<le>
 ltimeEnv
 (reset (setVarBool s0 hands hands_value) Ctrl)
Ctrl) 
\<longrightarrow>
inv0
 (toEnv 
(setPstate 
(reset (setVarBool s0 hands hands_value) Ctrl)
Ctrl
waiting))"

definition VC5 where
"VC5 inv0 s0 hands_value \<equiv>
(inv0 s0 \<and>
env (setVarBool s0 hands hands_value) hands_value) \<and>
(getPstate (setVarBool s0 hands hands_value) Ctrl = drying
\<and> getVarBool (setVarBool s0 hands hands_value) hands = ON
\<and>
\<not> (10 \<le>
 ltimeEnv
 (reset (setVarBool s0 hands hands_value) Ctrl)
Ctrl)) 
\<longrightarrow>
inv0
 (toEnv (reset (setVarBool s0 hands hands_value) Ctrl))"


definition VC6 where
"VC6 inv0 s0 hands_value \<equiv>
(inv0 s0 \<and>
env (setVarBool s0 hands hands_value) hands_value) \<and>
(getPstate (setVarBool s0 hands hands_value) Ctrl = drying
\<and> getVarBool (setVarBool s0 hands hands_value) hands \<noteq> ON
\<and>
 10 \<le>
 ltimeEnv
  (setVarBool s0 hands hands_value)
Ctrl) 
\<longrightarrow>
inv0
 (toEnv 
(setPstate (setVarBool s0 hands hands_value) Ctrl waiting)
)"

definition VC7 where
"VC7 inv0 s0 hands_value \<equiv>
(inv0 s0 \<and>
env (setVarBool s0 hands hands_value) hands_value) \<and>
(getPstate (setVarBool s0 hands hands_value) Ctrl = drying
\<and> getVarBool (setVarBool s0 hands hands_value) hands \<noteq> ON
\<and>
\<not> (10 \<le>
 ltimeEnv
 (setVarBool s0 hands hands_value)
Ctrl)) 
\<longrightarrow>
inv0  (toEnv (setVarBool s0 hands hands_value))"

end
