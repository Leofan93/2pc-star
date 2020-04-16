  
---------------------------- MODULE 2PC-star ----------------------------

EXTENDS Integers, Sequences, Bags, TLC

\* The set of transaction keys 
 CONSTANTS  VALUE

\* The set of client to execute a transaction
CONSTANTS  RM

\* next_ts is the timestamp for transaction. It is increased monotonically so
\* every transaction must have a unique start and commit ts.
VARIABLES  ascend_v

\* $client_state[c] is the state of client
VARIABLES  rm_status

\* $client_ts[c] is a record of [start: ts, commit: ts]
VARIABLES  commit_v

\* $client_keys[c] is a record of [primary: key, second: {key}]
 VARIABLES  rm_v

\* $key_lock[k] is the set of lock. 
VARIABLES  rm_lock

\* $key_write[k] is a sequence of committed version of the key.
VARIABLES  begin_v

\* $key_data[k] is the set of multi-version data timestamp of the key. 
 VARIABLES  rm_value

 Init == 
  /\  rm_status = [r \in RM|-> "beginning"]
  /\  rm_v = [r \in RM| -> [begin_v |-> 0, commit_v |-> 0]]
  /\  rm_value = [r \in RM| -> [first_val|-> "", second_val|->""]]
  /\  rm_lock = [v \in VALUE |->{}]
  /\  rm_data = [v \in VALUE |-> {}]
  /\  ascend_v = 0
  /\  committed_value = [v \in VALUE |-> <<>>]


       
key_vars == <<key_lock, key_write, key_data>>
client_txn_vars == <<client_ts, client_key>>

 Begin(r) == 
  /\  rm_status[r] = "beginning"
  /\  rm_status' = [rm_status  EXCEPT ![r] = "preparing "]
  /\  ascend_v' = ascend_v + 1
  /\  rm_value' =  [rm_value  EXCEPT ![r] = getVal]
  /\  rm_v' = [rm_v  EXCEPT !. begin_v = ascend_v']



\* Check whether there is a lock which start ts is less or equal than start_ts.
hasLockLE(k, start_ts) == 
    {l \in key_lock[k] : l.start_ts <= start_ts} /= {}

\* Check whether there is a lock with start ts or not.
hasLockEQ(k, start_ts) ==
     {l \in key_lock[k] : l.start_ts <= start_ts} /= {}
     
\* Select a primary key and use the rest for the secondary key
chooseKey ==
    LET
        primary == CHOOSE k \in KEY: TRUE
    IN
        [primary |-> primary, secondary |-> KEY \ {primary}]

\* Return TRUE means the client meets no lock and can does pre-write.     
canPrewrite(c) == 
     LET 
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary
     IN
        /\ ~hasLockLE(primary, start_ts)
        /\ \A k \in secondary : 
            /\ ~hasLockLE(k, start_ts)
           
\* Return TRUE means a lock can be cleanup up if:
\*  1. The lock is a primary lock and the start ts is less than start_ts.
\*  2. Or the lock is a secondary lock and the associated primary key is cleaned up. 
\* Notice: Percolator paper doesn't explain how to clean up the lock, here we just use 
\* a simple way.
isStaleLock(l, start_ts) ==            
    \/ /\ l.primary = ""
       /\ l.start_ts < start_ts
    \/ /\ l.primary /= ""
       /\ ~hasLockEQ(l.primary, l.start_ts) 
   
\* Return TRUE if we have a stale lock for key.
hasStaleLock(k, start_ts) ==
    \A l \in key_lock[k] :
        \/ isStaleLock(l, start_ts)                       
           
\* Return TRUE means the client can clean up a stale lock
canCleanup(c) == 
     LET 
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary
     IN
        /\ ~hasStaleLock(primary, start_ts)
        /\ \A k \in secondary : 
            /\ ~hasStaleLock(k, start_ts) 
            
\* Find write with start ts.
findWriteWithStart(k, start_ts) ==
    SelectSeq(key_write[k], LAMBDA w : w.start_ts = start_ts)  

\* Clean up a stale lock and its data. If the lock is a secondary lock
\* and the assoicated primary lock is cleaned up, we can clean up the lock and do:
\* 1. If the primary key is committed, we must also commit the secondary key
\* 2. Otherwise, clean up the stale data too
cleanupStaleLock(k, start_ts) == 
    LET
        \* Find a stale lock at first
        l == CHOOSE l \in key_lock[k] : isStaleLock(l, start_ts)
    IN
        /\ key_lock' = key_lock \ {l}
        /\ \/ /\ l.primary = ""
              /\ key_data' = key_data \ {l.start_ts}
              /\ UNCHANGED <<key_write>>
           \/ /\ l.primary /= ""
              /\ LET
                    w == findWriteWithStart(l.primary, l.start_ts)
                 IN
                    IF Len(w) = 0 
                    THEN
                        \* The primary key is not committed, clean up the data
                        /\ key_data' = key_data \ {l.start_ts}
                        /\ UNCHANGED <<key_write>>
                    ELSE
                        \* The primary key is committed, commit the secondary key
                        /\ key_write' = Append(key_write, w[1])
                        /\ UNCHANGED <<key_data>>

\* Clean up a stale lock when the client meets.
cleanup(c) == 
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary
        meetStaleLock(k) == /\ \/ k = primary 
                               \/ k \in secondary
                            /\ hasStaleLock(k, start_ts)   
        k == CHOOSE k \in KEY : meetStaleLock(k)
     IN
        cleanupStaleLock(k, start_ts)
        
\* Return TURE means there is no lock for key and no any newer write.
canLockKey(k, start_ts) ==    
    LET
        writes == {w \in DOMAIN key_write[k] : key_write[k][w].commit_ts >= start_ts}
    IN
        \* No any lock for the key
        /\ key_lock[k] = {} 
        \* No any newer write
        /\ writes = {} 
       
\* Return whether the client can lock all keys    
canLock(c) ==
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary 
    IN
        /\ canLockKey(primary, start_ts)
        /\ \A k \in secondary :
           /\ canLockKey(k, start_ts)

\* Lock the key and save the data
lockKey(k, start_ts, primary) ==
    /\ key_lock' = [key_lock EXCEPT ![k] = @ \UNION {[start_ts |-> start_ts, primary |-> primary]}]
    /\ key_data' = [key_data EXCEPT ![k] = @ \UNION {start_ts}]
    /\ UNCHANGED <<key_write>>
    

\* Try to lock primary key first, then the secondary key            
lock(c) == 
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary        
     IN
        IF hasLockEQ(primary, start_ts)
        THEN
            lockKey(primary, start_ts, "")
        ELSE
            \* primary key has already been locked, we must choose the a secondary key to lock
            LET
                k == CHOOSE k \in secondary : canLockKey(k, start_ts)
            IN
                lockKey(k, start_ts, primary)           
           
\* Return TRUE when the client locks all keys
canCommit(c) == 
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
        secondary == client_key[c].secondary
    IN
        /\ hasLockEQ(primary, start_ts)
        /\ \A k \in secondary : 
            /\ hasLockEQ(k, start_ts)

\* Return TRUE mean we can commit the primary key.
canCommitPrimary(c) ==
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
    IN
        hasLockEQ(primary, start_ts)
        
\* Commit the primary key.       
commitPrimary(c) == 
    LET
        start_ts == client_ts[c].start_ts
        primary == client_key[c].primary
    IN
        /\ key_write' = [key_write EXCEPT ![primary] = Append(@, client_ts[c])]
        /\ key_lock' = [key_lock EXCEPT ![primary] = @ \ {start_ts}] 
            
Start(c) ==
    /\ client_state[c] = "init"
    /\ client_state' = [client_state EXCEPT ![c] = "working"]
    /\ next_ts' = next_ts + 1
    /\ client_ts' = [client_ts EXCEPT ![c] = [@ EXCEPT !.start_ts = next_ts']]
    /\ client_key' = [client_key EXCEPT ![c] = chooseKey]
    /\ UNCHANGED <<key_vars>>

Loading(r) == 
  /\  rm_status[r] = "preparing"
  /\  IF  isPreCommit(r)
            THEN 
        /\  rm_status ' = [rm_status EXCEPT ![r] = "precommit"]
            ELSE 
        IF isResetLock (r)
               THEN 
            /\  resetLock(r)
               ELSE
            /\  rm_status' = [rm_status EXCEPT ![r] = "cancel"]

PreCommit(r) == 
  /\  rm_status[r] = " precommit "
  /\  IF  canCommit(r)
            THEN 
        /\  ascend_v' = ascend_v + 1
        /\  rm_v' = [rm_v  EXCEPT !. commit_v = ascend_v']
        /\  rm_status ' = [rm_status  EXCEPT ![r] = "committing"]
            ELSE  
         IF isAllLock(r)
                THEN 
             /\  allLock(r)
                ELSE 
             /\  rm_status ' = [rm_status EXCEPT ![r] = "cancel"]

Commit(r) == 
  /\  rm_status[r] = "committing"
  /\  IF  isCommitFirstVal(r) 
               THEN   
         /\  commitFirstVal(r)
         /\  rm_status ' = [rm_status EXCEPT ![r] = "committed "]
               ELSE
           /\  rm_status ' = [rm_status EXCEPT ![r] = "cancel "]

getVal == 
            LET  first_val== CHOOSE v \in VALUE: TRUE
    IN   [first_val |-> first_val, second_val |-> VALUE \ { first_val }]

isPreCommit(r) ==
          LET  begin_v = rm_v[r].begin_v
        first_val = rm_val[r].first_val
        second_val = rm_val[r].second_val
          IN
     /\  conformLock(first_val , begin_v)
     /\  \A s \in second_val: 
            /\  conformLock (s , begin_v)

 conformLock(first_val, begin_v) == 
                 { l \in lock[first _val ] : l. begin_v <= begin_v }

isResetLock(r) == 
           LET  begin_v = rm_v[r].begin_v
         first_val = rm_val[r].first_val
         second_val = rm_val[r].second_val
           IN  
      /\  existExpiredLock(first_val , begin_v)
      /\  \A s \in second_val:
             /\  existOldLock (s , begin_v)

existExpiredLock (second_val, begin_v) == 
     \A l \in lock[second _val ] :
        \/  isExpiredLock(l, begin_v)
isExpiredLock(l, begin_v) ==
     \/ /\     l.first_val = ""
       /\    l.begin_v < begin_v
     \/ /\    l.first_val = ""
       /\   conformLock (l. first_val, l.begin_v)

isAllLock(r) == 
   LET   begin_v = rm_v [r].begin_v
         first_val = rm_val[r].first_val
         second_val = rm_val[r].second_val
          IN
       /\   isLockValue(first_val, begin_v)
       /\   \A s \in second_val:
             /\   isLockValue(s , begin_v)

isLockValue(s , begin_v) == 
          LET 
      rms=={l \in  DOMAIN  committed_v[k]:
      committed_v[s][l].commit_t >= begin_v}
          IN
       /\    committed_v[s] = {}
       /\    rms = {}

isCommitFirstVal(r) ==
   LET   begin_v = rm_v[r].begin_v
         first_val = rm_val[r].first_val
   IN    conformLock(first_val, begin_v)
  
     commitFirstVal(r) == 
  LET   begin_v = rm_ts[r].begin_v
         first_val = rm_val[r].first_val
         IN  
     /\  committed_v' = [committed_v EXCEPT ![first_val] =    Append(@ , rm_v[r])]
     /\   lock' = [lock  EXCEPT ![first_val] = @ \{begin _v}]

Next == 
         \E r \in RM:
              Begin(r) \/ Loading(r) \/ PreCommit(r) \/ Commit(r)


CommittedConsistency == 
    \A c \in CLIENT :
    LET 
        start_ts == client_ts[c].start
        commit_ts == client_ts[c].commit
        primary == client_key[c].primary
        secondary == client_key[c].second
        w == [start |-> start_ts, commit |-> commit_ts]
    IN  
        \/ /\ client_state[c] = "committed"
           \* The primary key lock must be cleaned up, and no any older lock.
           /\ ~hasLockLE(primary, start_ts) 
           /\ findWriteWithCommit(primary, commit_ts) = <<w>>
           /\ {start_ts} \in key_data[primary]
           /\ \A k \in secondary :
              \* The secondary key lock can be empty or not.
              /\ \/ /\ ~hasLockEQ(k, start_ts)
                    /\ findWriteWithCommit(k, commit_ts) = <<w>>
                    /\ ~hasLockLE(k, start_ts - 1)
                 \/ /\ hasLockEQ(k, start_ts)
                    /\ findWriteWithCommit(k, commit_ts) = <<>>
                    /\ 
                        IF Len(key_write[k]) > 0 
                        THEN
                            \* Lock has not been cleaned up, so the last write committed 
                            \* timestamp must be less than lock start ts.
                            key_write[k][Len(key_write[k])].commit_ts < start_ts
                        ELSE
                            TRUE
              /\ {start_ts} \in key_data[k]
        \/ TRUE


