theory Requirements
  imports RevolvingDoor
begin

(*
1. При входе пользователя дверь начинает вращаться, если на перегородки
    не оказывается давление.
2. Вращение продолжается, пока пользователь находится внутри пространства 
   вращения, если на перегородки не оказывается давление.
3. Если пользователь покинул пространство вращения, то не более, чем через 
  DELAY секунд вращение остановится, если за это время пользователи 
  не появятся вновь.
4. Если на секционные перегородки оказывается давление, то вращение 
   приостанавливается не менее, чем на SUSPENSION_TIME секунд.
5. Если на секционные перегородки перестали оказывать давление, то не более, 
   чем через SUSPENSION_TIME секунд вращение возобновится.
6. Запрещена одновременная подача сигналов rotation и brake.
*)

definition R1 where "R1 s \<equiv> toEnvP s \<and> (\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and>
 toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 rotation = False \<and> getVarBool s2 user \<and> \<not> getVarBool s2 pressure \<longrightarrow>
 getVarBool s2 rotation = True)"

definition R2 where "R2 s \<equiv> toEnvP s \<and> (\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and>
 toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and>
 getVarBool s1 rotation = True \<and> getVarBool s2 user \<and> \<not> getVarBool s2 pressure \<longrightarrow>
 getVarBool s2 rotation = True)"

definition R3 where "R3 s \<equiv> toEnvP s \<and> (\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and>
toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s \<ge> DELAY'TIMEOUT \<and>
getVarBool s1 rotation = True \<and> \<not> getVarBool s2 user \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> DELAY'TIMEOUT \<and>
(getVarBool s4 rotation = False \<or> getVarBool s4 user) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow>  getVarBool s3 rotation = True \<and> \<not> getVarBool s3 user)))"

definition R4 where "R4 s \<equiv> toEnvP s \<and> (\<forall> s1 s2 s3. substate s1 s2 \<and> substate s2 s3 \<and> substate s3 s \<and>
toEnvP s1 \<and> toEnvP s2 \<and> toEnvP s3 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s3 < SUSPENSION_TIME'TIMEOUT \<and>
getVarBool s1 rotation = True \<and> getVarBool s2 pressure --> getVarBool s3 brake)"

definition R5 where "R5 s \<equiv> toEnvP s \<and> (\<forall> s1 s2. substate s1 s2 \<and> substate s2 s \<and>
toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s2 = 1 \<and> toEnvNum s2 s \<ge> SUSPENSION_TIME'TIMEOUT \<and>
getVarBool s1 brake \<and> \<not> getVarBool s2 pressure \<longrightarrow>
(\<exists> s4. toEnvP s4 \<and> substate s2 s4 \<and> substate s4 s \<and> toEnvNum s2 s4 \<le> SUSPENSION_TIME'TIMEOUT \<and>
(getVarBool s4 rotation = True \<or> getVarBool s4 pressure) \<and>
(\<forall> s3. toEnvP s3 \<and> substate s2 s3 \<and> substate s3 s4 \<and> s3 \<noteq> s4 \<longrightarrow> getVarBool s3 rotation = False \<and> \<not> getVarBool s3 pressure)))"

definition R6 where "R6 s \<equiv> toEnvP s \<and> (\<forall> s1. substate s1 s \<and> toEnvP s1 \<and> getVarBool s1 brake \<longrightarrow>
 getVarBool s1 rotation = False)"

definition env where "env s \<equiv> True"

end