theory RevolvingDoor imports Complex_Main
begin

type_synonym variable = nat
type_synonym process = nat
type_synonym pstate = nat

abbreviation user :: variable where "user \<equiv> (Suc 0)"
abbreviation pressure :: variable where "pressure \<equiv> (Suc (Suc 0))"
abbreviation rotation :: variable where "rotation \<equiv> (Suc (Suc (Suc 0)))"
abbreviation brake :: variable where "brake \<equiv> (Suc (Suc (Suc (Suc 0))))"

abbreviation Controller :: process where "Controller \<equiv> 1"

abbreviation STOP:: pstate where "STOP \<equiv> 0"
abbreviation ERROR:: pstate where "ERROR \<equiv> 1"

abbreviation Controller'rotating :: pstate where "Controller'rotating \<equiv> 3"
abbreviation Controller'motionless :: pstate where "Controller'motionless \<equiv> 2"
abbreviation Controller'suspended :: pstate where "Controller'suspended \<equiv> 4"

abbreviation SUSPENSION_TIME :: int where "SUSPENSION_TIME \<equiv> 1000"
abbreviation DELAY :: int where "DELAY \<equiv> 1000"

abbreviation SUSPENSION_TIME'TIMEOUT :: nat where "SUSPENSION_TIME'TIMEOUT \<equiv> 10"
abbreviation DELAY'TIMEOUT :: nat where "DELAY'TIMEOUT \<equiv> 10"

datatype state =
  emptyState |
  toEnv state |
  setVarBool state variable bool |
  setVarInt state variable int |
  setVarReal state variable real |
  setVarArrayBool state variable int bool |
  setVarArrayInt state variable int int |
  setVarArrayReal state variable int real |
  setVarAny state bool bool |
  setPstate state process pstate |
  reset state process

fun getVarBool:: "state => variable => bool" where
  "getVarBool emptyState _ = False" |
  "getVarBool (toEnv s') x' = getVarBool s' x'" |
  "getVarBool (setVarBool s' y' v') x' = (if x' = y' then v' else (getVarBool s' x'))" |
  "getVarBool (setVarInt s' _ _) x' = getVarBool s' x'" |
  "getVarBool (setVarReal s' _ _) x' = getVarBool s' x'" |
  "getVarBool (setVarArrayBool s' _ _ _) x' = getVarBool s' x'" |
  "getVarBool (setVarArrayInt s' _ _ _) x' = getVarBool s' x'" |
  "getVarBool (setVarArrayReal s' _ _ _) x' = getVarBool s' x'" |
  "getVarBool (setVarAny s'  user'value pressure'value) user = user'value" |
  "getVarBool (setVarAny s'  user'value pressure'value) pressure = pressure'value" |
  "getVarBool (setVarAny s'  user'value pressure'value) x' = getVarBool s' x'" |
  "getVarBool (setPstate s' _ _) x' = getVarBool s' x'" |
  "getVarBool (reset s' _) x' = getVarBool s' x'"

fun getVarInt:: "state => variable => int" where
  "getVarInt emptyState _ = 0" |
  "getVarInt (toEnv s') x' = getVarInt s' x'" |
  "getVarInt (setVarBool s' _ _) x' = getVarInt s' x'" |
  "getVarInt (setVarInt s' y' v') x' = (if x' = y' then v' else (getVarInt s' x'))" |
  "getVarInt (setVarReal s' _ _) x' = getVarInt s' x'" |
  "getVarInt (setVarArrayBool s' _ _ _) x' = getVarInt s' x'" |
  "getVarInt (setVarArrayInt s' _ _ _) x' = getVarInt s' x'" |
  "getVarInt (setVarArrayReal s' _ _ _) x' = getVarInt s' x'" |
  "getVarInt (setVarAny s'  user'value pressure'value) x' = getVarInt s' x'" |
  "getVarInt (setPstate s' _ _) x' = getVarInt s' x'" |
  "getVarInt (reset s' _) x' = getVarInt s' x'"

fun getVarReal:: "state => variable => real" where
  "getVarReal emptyState _ = 0" |
  "getVarReal (toEnv s') x' = getVarReal s' x'" |
  "getVarReal (setVarBool s' _ _) x' = getVarReal s' x'" |
  "getVarReal (setVarInt s' _ _) x' = getVarReal s' x'" |
  "getVarReal (setVarReal s' y' v') x' = (if x' = y' then v' else (getVarReal s' x'))" |
  "getVarReal (setVarArrayBool s' _ _ _) x' = getVarReal s' x'" |
  "getVarReal (setVarArrayInt s' _ _ _) x' = getVarReal s' x'" |
  "getVarReal (setVarArrayReal s' _ _ _) x' = getVarReal s' x'" |
  "getVarReal (setVarAny s'  user'value pressure'value) x' = getVarReal s' x'" |
  "getVarReal (setPstate s' _ _) x' = getVarReal s' x'" |
  "getVarReal (reset s' _) x' = getVarReal s' x'"

fun getVarArrayBool:: "state => variable => int => bool" where
  "getVarArrayBool emptyState _ _ = False" |
  "getVarArrayBool (toEnv s') x' i' = getVarArrayBool s' x' i'" |
  "getVarArrayBool (setVarBool s' _ _) x' i' = getVarArrayBool s' x' i'" |
  "getVarArrayBool (setVarInt s' _ _) x' i' = getVarArrayBool s' x' i'" |
  "getVarArrayBool (setVarReal s' _ _) x' i' = getVarArrayBool s' x' i'" |
  "getVarArrayBool (setVarArrayBool s' y' j' v') x' i' = (if x' = y' \<and> i' = j' then v' else (getVarArrayBool s' x' i'))" |
  "getVarArrayBool (setVarArrayInt s' _ _ _) x' i' = getVarArrayBool s' x' i'" |
  "getVarArrayBool (setVarArrayReal s' _ _ _) x' i' = getVarArrayBool s' x' i'" |
  "getVarArrayBool (setVarAny s'  user'value pressure'value) x' i' = getVarArrayBool s' x' i'" |
  "getVarArrayBool (setPstate s' _ _) x' i' = getVarArrayBool s' x' i'" |
  "getVarArrayBool (reset s' _) x' i' = getVarArrayBool s' x' i'"

fun getVarArrayInt:: "state => variable => int => int" where
  "getVarArrayInt emptyState _ _ = 0" |
  "getVarArrayInt (toEnv s') x' i' = getVarArrayInt s' x' i'" |
  "getVarArrayInt (setVarBool s' _ _) x' i' = getVarArrayInt s' x' i'" |
  "getVarArrayInt (setVarInt s' _ _) x' i' = getVarArrayInt s' x' i'" |
  "getVarArrayInt (setVarReal s' _ _) x' i' = getVarArrayInt s' x' i'" |
  "getVarArrayInt (setVarArrayBool s' _ _ _) x' i' = getVarArrayInt s' x' i'" |
  "getVarArrayInt (setVarArrayInt s' y' j' v') x' i' = (if x' = y' \<and> i' = j' then v' else (getVarArrayInt s' x' i'))" |
  "getVarArrayInt (setVarArrayReal s' _ _ _) x' i' = getVarArrayInt s' x' i'" |
  "getVarArrayInt (setVarAny s'  user'value pressure'value) x' i' = getVarArrayInt s' x' i'" |
  "getVarArrayInt (setPstate s' _ _) x' i' = getVarArrayInt s' x' i'" |
  "getVarArrayInt (reset s' _) x' i' = getVarArrayInt s' x' i'"

fun getVarArrayReal:: "state => variable => int => real" where
  "getVarArrayReal emptyState _ _ = 0" |
  "getVarArrayReal (toEnv s') x' i' = getVarArrayReal s' x' i'" |
  "getVarArrayReal (setVarBool s' _ _) x' i' = getVarArrayReal s' x' i'" |
  "getVarArrayReal (setVarInt s' _ _) x' i' = getVarArrayReal s' x' i'" |
  "getVarArrayReal (setVarReal s' _ _) x' i' = getVarArrayReal s' x' i'" |
  "getVarArrayReal (setVarArrayBool s' _ _ _) x' i' = getVarArrayReal s' x' i'" |
  "getVarArrayReal (setVarArrayInt s' _ _ _) x' i' = getVarArrayReal s' x' i'" |
  "getVarArrayReal (setVarArrayReal s' y' j' v') x' i' = (if x' = y' \<and> i' = j' then v' else (getVarArrayReal s' x' i'))" |
  "getVarArrayReal (setVarAny s'  user'value pressure'value) x' i' = getVarArrayReal s' x' i'" |
  "getVarArrayReal (setPstate s' _ _) x' i' = getVarArrayReal s' x' i'" |
  "getVarArrayReal (reset s' _) x' i' = getVarArrayReal s' x' i'"

fun getPstate:: "state => process => pstate" where
  "getPstate emptyState _ = 0" |
  "getPstate (toEnv s') p' = getPstate s' p'" |
  "getPstate (setVarBool s' _ _) p' = getPstate s' p'" |
  "getPstate (setVarInt s' _ _) p' = getPstate s' p'" |
  "getPstate (setVarReal s' _ _) p' = getPstate s' p'" |
  "getPstate (setVarArrayBool s' _ _ _) p' = getPstate s' p'" |
  "getPstate (setVarArrayInt s' _ _ _) p' = getPstate s' p'" |
  "getPstate (setVarArrayReal s' _ _ _) p' = getPstate s' p'" |
  "getPstate (setVarAny s'  user'value pressure'value) p' = getPstate s' p'" |
  "getPstate (setPstate s' p1' q') p' = (if p' = p1' then q' else (getPstate s' p'))" |
  "getPstate (reset s' _) p' = getPstate s' p'"

fun substate:: "state => state => bool" where
  "substate s' emptyState =
    (if s' = emptyState then True else False)" |
  "substate s' (toEnv s1') =
    (if s' = toEnv s1' then True else substate s' s1')" |
  "substate s' (setVarBool s1' x' v') = 
    (if s' = setVarBool s1' x' v' then True else substate s' s1')" |
  "substate s' (setVarInt s1' x' v') =
    (if s' = setVarInt s1' x' v' then True else substate s' s1')" |
  "substate s' (setVarReal s1' x' v') =
    (if s' = setVarReal s1' x' v' then True else substate s' s1')" |
  "substate s' (setVarArrayBool s1' x' i' v') =
    (if s' = setVarArrayBool s1' x' i' v' then True else substate s' s1')" |
  "substate s' (setVarArrayInt s1' x' i' v') =
    (if s' = setVarArrayInt s1' x' i' v' then True else substate s' s1')" |
  "substate s' (setVarArrayReal s1' x' i' v') =
    (if s' = setVarArrayReal s1' x' i' v' then True else substate s' s1')" |
  "substate s' (setVarAny s1'  user'value pressure'value) =
    (if s' = (setVarAny s1'  user'value pressure'value) then True else substate s' s1')" |
  "substate s' (setPstate s1' p' q') =
    (if s' = setPstate s1' p' q' then True else substate s' s1')" |
  "substate s' (reset s1' p') =
    (if s' = reset s1' p' then True else substate s' s1')"

fun toEnvNum:: "state => state => nat" where 
  "toEnvNum s' emptyState = 0" |
  "toEnvNum s' (toEnv s1') = 
    (if s' = toEnv s1' then 0 else toEnvNum s' s1' + 1)" |
  "toEnvNum s' (setVarBool s1' x' v') =
    (if s' = setVarBool s1' x' v' then 0 else toEnvNum s' s1')" |
  "toEnvNum s' (setVarInt s1' x' v') =
    (if s' = setVarInt s1' x' v' then 0 else toEnvNum s' s1')" |
  "toEnvNum s' (setVarReal s1' x' v') =
    (if s' = setVarReal s1' x' v' then 0 else toEnvNum s' s1')" |
  "toEnvNum s' (setVarArrayBool s1' x' i' v') =
    (if s' = setVarArrayBool s1' x' i' v' then 0 else toEnvNum s' s1')" |
  "toEnvNum s' (setVarArrayInt s1' x' i' v') =
    (if s' = setVarArrayInt s1' x' i' v' then 0 else toEnvNum s' s1')" |
  "toEnvNum s' (setVarArrayReal s1' x' i' v') =
    (if s' = setVarArrayReal s1' x' i' v' then 0 else toEnvNum s' s1')" |
  "toEnvNum s' (setVarAny s1'  user'value pressure'value) =
    (if s' = (setVarAny s1'  user'value pressure'value) then 0 else toEnvNum s' s1')" |
  "toEnvNum s' (setPstate s1' p' q') =
    (if s' = setPstate s1' p' q' then 0 else toEnvNum s' s1')" |
  "toEnvNum s' (reset s1' p') =
    (if s' = reset s1' p' then 0 else toEnvNum s' s1')"

fun toEnvP::"state => bool" where
  "toEnvP (toEnv _) = True" |
  "toEnvP _ = False"

fun ltime:: "state => process => nat" where 
  "ltime emptyState _ = 0" |
  "ltime (toEnv s') p' = (ltime s' p') + 1" |
  "ltime (setVarBool s' _ _) p' = ltime s' p'" |
  "ltime (setVarInt s' _ _) p' = ltime s' p'" |
  "ltime (setVarReal s' _ _) p' = ltime s' p'" |
  "ltime (setVarArrayBool s' _ _ _) p' = ltime s' p'" |
  "ltime (setVarArrayInt s' _ _ _) p' = ltime s' p'" |
  "ltime (setVarArrayReal s' _ _ _) p' = ltime s' p'" |
  "ltime (setVarAny s'  user'value pressure'value) p' = ltime s' p'" |
  "ltime (setPstate s' p1' _) p' = (if p' = p1' then 0 else ltime s' p')" |
  "ltime (reset s' p1') p' = (if p' = p1' then 0 else ltime s' p')"

fun predEnv:: "state => state" where
  "predEnv emptyState = emptyState" |
  "predEnv (toEnv s') =
    (if (toEnvP s') then s' else predEnv s')" |		
  "predEnv (setVarBool s' _ _) = 
    (if (toEnvP s') then s' else predEnv s')" |
  "predEnv (setVarInt s' _ _) = 
    (if (toEnvP s') then s' else predEnv s')" |
  "predEnv (setVarReal s' _ _) = 
    (if (toEnvP s') then s' else predEnv s')" |
  "predEnv (setVarArrayBool s' _ _ _) = 
    (if (toEnvP s') then s' else predEnv s')" |
  "predEnv (setVarArrayInt s' _ _ _) = 
    (if (toEnvP s') then s' else predEnv s')" |
  "predEnv (setVarArrayReal s' _ _ _) = 
    (if (toEnvP s') then s' else predEnv s')" |
  "predEnv (setVarAny s'  user'value pressure'value) = 
    (if (toEnvP s') then s' else predEnv s')" |
  "predEnv (setPstate s' _ _) = 
    (if (toEnvP s') then s' else predEnv s')" |
  "predEnv (reset s' _) = 
    (if (toEnvP s') then s' else predEnv s')"

fun shift:: "state => nat => state" where
  "shift s' 0 = s'" |
  "shift s' (Suc n') = predEnv (shift s' n')"

(*Verification conditions*)


definition VC1 where
  "VC1 inv' s0' \<equiv>
  (
    (
      s0'
    =
      (toEnv
        (setPstate
          emptyState
          Controller
          Controller'motionless
        )
      )
    )
  -->
    (inv'
      s0'
    )
  )
  "

definition VC2 where
  "VC2 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (inv'
              s0'
            )
          \<and>
            (env'
              (setVarAny
                s0'
                user'value
                pressure'value
              )
            )
          )
        \<and>
          (
            (getPstate
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              Controller
            )
          =
            Controller'motionless
          )
        )
      \<and>
        (getVarBool
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          user
        )
      )
    \<and>
      (getVarBool
        (setVarAny
          s0'
          user'value
          pressure'value
        )
        pressure
      )
    )
  -->
    (inv'
      (toEnv
        (setPstate
          (setVarBool
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            brake
            True
          )
          Controller
          Controller'suspended
        )
      )
    )
  )
  "

definition VC3 where
  "VC3 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (inv'
              s0'
            )
          \<and>
            (env'
              (setVarAny
                s0'
                user'value
                pressure'value
              )
            )
          )
        \<and>
          (
            (getPstate
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              Controller
            )
          =
            Controller'motionless
          )
        )
      \<and>
        (getVarBool
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          user
        )
      )
    \<and>
      (\<not>
        (getVarBool
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          pressure
        )
      )
    )
  -->
    (inv'
      (toEnv
        (setPstate
          (setVarBool
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            rotation
            True
          )
          Controller
          Controller'rotating
        )
      )
    )
  )
  "

definition VC4 where
  "VC4 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (inv'
            s0'
          )
        \<and>
          (env'
            (setVarAny
              s0'
              user'value
              pressure'value
            )
          )
        )
      \<and>
        (
          (getPstate
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            Controller
          )
        =
          Controller'motionless
        )
      )
    \<and>
      (\<not>
        (getVarBool
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          user
        )
      )
    )
  -->
    (inv'
      (toEnv
        (setVarAny
          s0'
          user'value
          pressure'value
        )
      )
    )
  )
  "

definition VC5 where
  "VC5 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (inv'
              s0'
            )
          \<and>
            (env'
              (setVarAny
                s0'
                user'value
                pressure'value
              )
            )
          )
        \<and>
          (
            (getPstate
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              Controller
            )
          =
            Controller'rotating
          )
        )
      \<and>
        (getVarBool
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          pressure
        )
      )
    \<and>
      (
        DELAY'TIMEOUT
      <=
        (ltime
          (setPstate
            (setVarBool
              (setVarBool
                (setVarAny
                  s0'
                  user'value
                  pressure'value
                )
                rotation
                False
              )
              brake
              True
            )
            Controller
            Controller'suspended
          )
          Controller
        )
      )
    )
  -->
    (inv'
      (toEnv
        (setPstate
          (setVarBool
            (setPstate
              (setVarBool
                (setVarBool
                  (setVarAny
                    s0'
                    user'value
                    pressure'value
                  )
                  rotation
                  False
                )
                brake
                True
              )
              Controller
              Controller'suspended
            )
            rotation
            False
          )
          Controller
          Controller'motionless
        )
      )
    )
  )
  "

definition VC6 where
  "VC6 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (inv'
              s0'
            )
          \<and>
            (env'
              (setVarAny
                s0'
                user'value
                pressure'value
              )
            )
          )
        \<and>
          (
            (getPstate
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              Controller
            )
          =
            Controller'rotating
          )
        )
      \<and>
        (getVarBool
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          pressure
        )
      )
    \<and>
      (\<not>
        (
          DELAY'TIMEOUT
        <=
          (ltime
            (setPstate
              (setVarBool
                (setVarBool
                  (setVarAny
                    s0'
                    user'value
                    pressure'value
                  )
                  rotation
                  False
                )
                brake
                True
              )
              Controller
              Controller'suspended
            )
            Controller
          )
        )
      )
    )
  -->
    (inv'
      (toEnv
        (setPstate
          (setVarBool
            (setVarBool
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              rotation
              False
            )
            brake
            True
          )
          Controller
          Controller'suspended
        )
      )
    )
  )
  "

definition VC7 where
  "VC7 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (
              (inv'
                s0'
              )
            \<and>
              (env'
                (setVarAny
                  s0'
                  user'value
                  pressure'value
                )
              )
            )
          \<and>
            (
              (getPstate
                (setVarAny
                  s0'
                  user'value
                  pressure'value
                )
                Controller
              )
            =
              Controller'rotating
            )
          )
        \<and>
          (\<not>
            (getVarBool
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              pressure
            )
          )
        )
      \<and>
        (getVarBool
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          user
        )
      )
    \<and>
      (
        DELAY'TIMEOUT
      <=
        (ltime
          (reset
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            Controller
          )
          Controller
        )
      )
    )
  -->
    (inv'
      (toEnv
        (setPstate
          (setVarBool
            (reset
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              Controller
            )
            rotation
            False
          )
          Controller
          Controller'motionless
        )
      )
    )
  )
  "

definition VC8 where
  "VC8 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (
              (inv'
                s0'
              )
            \<and>
              (env'
                (setVarAny
                  s0'
                  user'value
                  pressure'value
                )
              )
            )
          \<and>
            (
              (getPstate
                (setVarAny
                  s0'
                  user'value
                  pressure'value
                )
                Controller
              )
            =
              Controller'rotating
            )
          )
        \<and>
          (\<not>
            (getVarBool
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              pressure
            )
          )
        )
      \<and>
        (getVarBool
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          user
        )
      )
    \<and>
      (\<not>
        (
          DELAY'TIMEOUT
        <=
          (ltime
            (reset
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              Controller
            )
            Controller
          )
        )
      )
    )
  -->
    (inv'
      (toEnv
        (reset
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          Controller
        )
      )
    )
  )
  "

definition VC9 where
  "VC9 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (
              (inv'
                s0'
              )
            \<and>
              (env'
                (setVarAny
                  s0'
                  user'value
                  pressure'value
                )
              )
            )
          \<and>
            (
              (getPstate
                (setVarAny
                  s0'
                  user'value
                  pressure'value
                )
                Controller
              )
            =
              Controller'rotating
            )
          )
        \<and>
          (\<not>
            (getVarBool
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              pressure
            )
          )
        )
      \<and>
        (\<not>
          (getVarBool
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            user
          )
        )
      )
    \<and>
      (
        DELAY'TIMEOUT
      <=
        (ltime
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          Controller
        )
      )
    )
  -->
    (inv'
      (toEnv
        (setPstate
          (setVarBool
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            rotation
            False
          )
          Controller
          Controller'motionless
        )
      )
    )
  )
  "

definition VC10 where
  "VC10 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (
              (inv'
                s0'
              )
            \<and>
              (env'
                (setVarAny
                  s0'
                  user'value
                  pressure'value
                )
              )
            )
          \<and>
            (
              (getPstate
                (setVarAny
                  s0'
                  user'value
                  pressure'value
                )
                Controller
              )
            =
              Controller'rotating
            )
          )
        \<and>
          (\<not>
            (getVarBool
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              pressure
            )
          )
        )
      \<and>
        (\<not>
          (getVarBool
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            user
          )
        )
      )
    \<and>
      (\<not>
        (
          DELAY'TIMEOUT
        <=
          (ltime
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            Controller
          )
        )
      )
    )
  -->
    (inv'
      (toEnv
        (setVarAny
          s0'
          user'value
          pressure'value
        )
      )
    )
  )
  "

definition VC11 where
  "VC11 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (inv'
              s0'
            )
          \<and>
            (env'
              (setVarAny
                s0'
                user'value
                pressure'value
              )
            )
          )
        \<and>
          (
            (getPstate
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              Controller
            )
          =
            Controller'suspended
          )
        )
      \<and>
        (getVarBool
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          pressure
        )
      )
    \<and>
      (
        SUSPENSION_TIME'TIMEOUT
      <=
        (ltime
          (reset
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            Controller
          )
          Controller
        )
      )
    )
  -->
    (inv'
      (toEnv
        (setPstate
          (setVarBool
            (setVarBool
              (reset
                (setVarAny
                  s0'
                  user'value
                  pressure'value
                )
                Controller
              )
              brake
              False
            )
            rotation
            True
          )
          Controller
          Controller'rotating
        )
      )
    )
  )
  "

definition VC12 where
  "VC12 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (inv'
              s0'
            )
          \<and>
            (env'
              (setVarAny
                s0'
                user'value
                pressure'value
              )
            )
          )
        \<and>
          (
            (getPstate
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              Controller
            )
          =
            Controller'suspended
          )
        )
      \<and>
        (getVarBool
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          pressure
        )
      )
    \<and>
      (\<not>
        (
          SUSPENSION_TIME'TIMEOUT
        <=
          (ltime
            (reset
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              Controller
            )
            Controller
          )
        )
      )
    )
  -->
    (inv'
      (toEnv
        (reset
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          Controller
        )
      )
    )
  )
  "

definition VC13 where
  "VC13 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (inv'
              s0'
            )
          \<and>
            (env'
              (setVarAny
                s0'
                user'value
                pressure'value
              )
            )
          )
        \<and>
          (
            (getPstate
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              Controller
            )
          =
            Controller'suspended
          )
        )
      \<and>
        (\<not>
          (getVarBool
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            pressure
          )
        )
      )
    \<and>
      (
        SUSPENSION_TIME'TIMEOUT
      <=
        (ltime
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          Controller
        )
      )
    )
  -->
    (inv'
      (toEnv
        (setPstate
          (setVarBool
            (setVarBool
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              brake
              False
            )
            rotation
            True
          )
          Controller
          Controller'rotating
        )
      )
    )
  )
  "

definition VC14 where
  "VC14 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (
          (
            (inv'
              s0'
            )
          \<and>
            (env'
              (setVarAny
                s0'
                user'value
                pressure'value
              )
            )
          )
        \<and>
          (
            (getPstate
              (setVarAny
                s0'
                user'value
                pressure'value
              )
              Controller
            )
          =
            Controller'suspended
          )
        )
      \<and>
        (\<not>
          (getVarBool
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            pressure
          )
        )
      )
    \<and>
      (\<not>
        (
          SUSPENSION_TIME'TIMEOUT
        <=
          (ltime
            (setVarAny
              s0'
              user'value
              pressure'value
            )
            Controller
          )
        )
      )
    )
  -->
    (inv'
      (toEnv
        (setVarAny
          s0'
          user'value
          pressure'value
        )
      )
    )
  )
  "

definition VC15 where
  "VC15 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (inv'
          s0'
        )
      \<and>
        (env'
          (setVarAny
            s0'
            user'value
            pressure'value
          )
        )
      )
    \<and>
      (
        (getPstate
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          Controller
        )
      =
        STOP
      )
    )
  -->
    (inv'
      (toEnv
        (setVarAny
          s0'
          user'value
          pressure'value
        )
      )
    )
  )
  "

definition VC16 where
  "VC16 inv' env' s0' user'value pressure'value \<equiv>
  (
    (
      (
        (inv'
          s0'
        )
      \<and>
        (env'
          (setVarAny
            s0'
            user'value
            pressure'value
          )
        )
      )
    \<and>
      (
        (getPstate
          (setVarAny
            s0'
            user'value
            pressure'value
          )
          Controller
        )
      =
        ERROR
      )
    )
  -->
    (inv'
      (toEnv
        (setVarAny
          s0'
          user'value
          pressure'value
        )
      )
    )
  )
  "
end
