theory Requirements
imports HandDryer
begin

definition R1 where
"R1 s \<equiv>
toEnvP s \<and>
(\<forall> s1 s2.  substate s1 s2 \<and>
 substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and>
 toEnvNum s1 s2 = 1 \<and> 
getVarBool s1 hands = OFF \<and>
 getVarBool s1 dryer = OFF \<and>
getVarBool s2 hands = ON \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s\<and>
toEnvNum s2 s4 \<le> 1 \<and> getVarBool s4 dryer = ON \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and>
 substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
 getVarBool s3 hands = ON)))"

definition R2 where
"R2 s \<equiv>
toEnvP s \<and> ( \<forall>s1 s2.  substate s1 s2 \<and>
 substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and>
 toEnvNum s1 s2 = 1 \<and> getVarBool s1 dryer = OFF \<and>
getVarBool s2 hands = OFF \<longrightarrow>
 getVarBool s2 dryer = OFF)"


definition R3 where
"R3 s \<equiv>
toEnvP s \<and>
(\<forall> s1 s2.  substate s1 s2 \<and>
 substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and>
 toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s \<ge> 10 \<and>
getVarBool s1 hands = ON \<and>
 getVarBool s1 dryer = ON \<and>
getVarBool s2 hands = OFF \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s\<and>
toEnvNum s2 s4 \<le> 10 \<and> 
(getVarBool s4 dryer = OFF \<or> 
getVarBool s4 hands = ON) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and>
 substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
 getVarBool s3 dryer = ON \<and>
getVarBool s3 hands = OFF)))"

definition R4 where
"R4 s \<equiv>
toEnvP s \<and>
(\<forall> s1 s2.  substate s1 s2 \<and>
 substate s2 s \<and> toEnvP s1 \<and> toEnvP s2 \<and>
 toEnvNum s1 s2 = 1 \<and> getVarBool s1 dryer = ON \<and>
getVarBool s2 hands = ON \<longrightarrow>
 getVarBool s2 dryer = ON)"

definition R5 where
"R5 s k \<equiv>
\<forall> s1 s3. substate s1 s3 \<and> substate s3 s \<and>
 toEnvNum s1 s3 > k \<longrightarrow>
(\<exists> s2. substate s1 s2 \<and> substate s2 s3 \<and>
 getVarBool s2 dryer = OFF)"

definition extraInv where
"extraInv s \<equiv>
toEnvP s \<and> 
(getPstate s Ctrl = drying \<longrightarrow> 
0 < ltimeEnv s Ctrl \<and> ltimeEnv s Ctrl \<le> 10 \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and>
 toEnvNum s1 s + 1 = ltimeEnv s Ctrl \<longrightarrow>
getVarBool s1 hands = ON \<and>
 getVarBool s1 dryer = ON) \<and> 
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<and>
 toEnvNum s1 s + 1 < ltimeEnv s Ctrl \<longrightarrow>
getVarBool s1 hands = OFF \<and>
 getVarBool s1 dryer = ON)) \<and>
(\<forall> s1. toEnvP s1 \<and> substate s1 s \<longrightarrow>
getPstate s1 Ctrl = waiting \<or>
getPstate s1 Ctrl = drying)"

definition inv1 where "inv1 s \<equiv> R1 s \<and> extraInv s"
definition inv2 where "inv2 s \<equiv> R2 s \<and> extraInv s"
definition inv3 where "inv3 s \<equiv> R3 s \<and> extraInv s"
definition inv4 where "inv4 s = (R4 s \<and> extraInv s)"
definition inv5 where "inv5 s k \<equiv> R5 s k \<and> extraInv s"

definition pred3 where
"pred3 s2 s s5 \<equiv>
(\<forall>s3. toEnvP s3 \<and>
               substate s2 s3 \<and>
               substate s3 s5 \<and> s3 \<noteq> s5 \<longrightarrow>
               getVarBool s3 (Suc (Suc 0)) = ON \<and>
               getVarBool s3 hands = OFF) \<longrightarrow>
(\<exists>s4. toEnvP s4 \<and>
            substate s5 s4 \<and>
            substate s4 s \<and>
            toEnvNum s2 s4 \<le> 10 \<and>
            (getVarBool s4 (Suc (Suc 0)) = OFF \<or>
             getVarBool s4 hands = ON) \<and>
            (\<forall>s3. toEnvP s3 \<and>
                  substate s5 s3 \<and>
                  substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>
                  getVarBool s3 (Suc (Suc 0)) = ON \<and>
                  getVarBool s3 hands = OFF))"