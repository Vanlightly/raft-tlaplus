# Standard Raft TLA+ specifications

The following specs have been created:
- Raft (no reconfiguration)
- Raft with joint consensus reconfiguration
- Raft with add/remove reconfiguration

## Points of interest

### Reusing server identities after removal from clusters

The Raft algorithm does not tolerate bringing back a node without its state. So if the data disk of a node failed and the administrator brought the node back up with an empty disk and the same server identity then data loss can result. This is well known. Instead the administrator should use Raft reconfiguration to remove the node and then add it back again.

However what is not well known is that adding a blank node with the same identity, even after having been removed can still result in data loss. The issue lies in that a reconfiguration is committed based on majorities - meaning that there can be nodes that are still on the old configuration. There are behaviours (histories) where after two reconfigurations, an administrator brings back a removed node without state but the same identity and it ends up voting for a peer who is still in a previous configuration.

The most obvious fix is to ensure that servers generate a unique id on boot from blank state. This can be leveraged in two useful ways:
- the server cannot receive RPCs of a prior incarnation (thus avoiding the two example below).
- tying the log data path on disk to the unique id prevents a server from being accidentally started with no state. For example, an administrator borking the volume mounts and the server starting with no prior state. In this case the server would generate a new id and not participate in any existing Raft clusters. Once the administrator realises the mistake and fixes the volume mounts, the server can be restarted with the correct identity and all its data.

#### Raft with joint consensus reconfiguration - split brain example

An example history:

Initial state:
```
Servers: {s1, s2, s3, s4, s5}
Cluster: {s1, s2, s3 }, leader is s3
s1 has become unroutable (weird EC2 issue).
```

Step 1: Leader adds OldNewConfigCommand to replace s1 with s4 and replicates to a majority of the old and a majority of the new config.
```
s1: c1{s1, s2, s3} unreachable
s2: c2 old{s1, s2, s3}, new{s2, s3, s4}
s3: c2 old{s1, s2, s3}, new{s2, s3, s4} Leader
s4: c2 old{s1, s2, s3}, new{s2, s3, s4}
s5: {}
```

Step 2: Leader adds NewConfigCommand to commit the reconfig and replicates to a majority of the new configuration.
```
s1: c1 {s1, s2, s3} unreachable
s2: c2 old{s1, s2, s3}, new{s2, s3, s4}
s3: c3 {s2, s3, s4} Leader
s4: c3 {s2, s3, s4}
s5: {}
```

Step 3: s2 data disk failure. Leader adds OldNewConfigCommand to replace s2 with s5 and replicates to a majority of the old and a majority of the new config.
```
s1: c1{s1, s2, s3} unreachable
s2: c2 old{s1, s2, s3}, new{s2, s3, s4} failed
s3: c4 old{s2, s3, s4}, new{s3, s4, s5} Leader
s4: c4 old{s2, s3, s4}, new{s3, s4, s5}
s5: c4 old{s2, s3, s4}, new{s3, s4, s5}
```

Step 4: Leader adds NewConfigCommand to commit the reconfig and replicates to a majority of the new configuration.
```
s1: c1{s1, s2, s3} unreachable
s2: c2 old{s1, s2, s3}, new{s2, s3, s4} failed
s3: c5{s3, s4, s5} Leader
s4: c5{s3, s4, s5}
s5: c5{s3, s4, s5}
```

Step 5: Administrator brings back s2 with a new disk and the same identity.
```
s1: c1{s1, s2, s3} unreachable
s2: {}
s3: c5{s3, s4, s5} Leader
s4: c5{s3, s4, s5}
s5: c5{s3, s4, s5}
```

Step 6: s1 becomes reachable again and it starts an election. s2 votes for s1 and s2 still being on the first configuration has a majority and becomes leader. s1 replicates
to s2 and s2 truncates it log, assuming configuration c1.
```
s1: c1{s1, s2, s3} Leader
s2: c1{s1, s2, s3}
s3: c5{s3, s4, s5} Leader
s4: c5{s3, s4, s5}
s5: c5{s3, s4, s5}
```

#### Raft with add/remove reconfiguration - split brain example

An example history:

Initial state:
```
Servers: {s1, s2, s3, s4, s5}
Cluster: {s1, s2, s3 }, leader is s3
s1 has become unroutable (weird EC2 issue).
```

Step 1: Leader adds AddServerCommand to add s4 and replicates to a majority of the new configuration.
```
s1: c1{s1, s2, s3 } unreachable
s2: c2{s1, s2, s3, s4}
s3: c2{s1, s2, s3, s4} Leader
s4: c2{s1, s2, s3, s4}
s5: {}
```

Step 2: Leader adds RemoveServerCommand to remove s1 and replicates to a majority of the new configuration.
```
s1: c1{s1, s2, s3} unreachable
s2: c2{s1, s2, s3, s4}
s3: c3{s2, s3, s4} Leader
s4: c3{s2, s3, s4}
s5: {}
```

Step 3: s2 data disk failure. Leader adds AddServerCommand to add s5 and replicates to a majority of the new configuration.
```
s1: c1{s1, s2, s3}  unreachable
s2: c2{s1, s2, s3, s4} offline
s3: c4{s2, s3, s4, s5} Leader
s4: c4{s2, s3, s4, s5}
s5: c4{s2, s3, s4, s5}
```

Step 4: Leader adds RemoveServerCommand to remove s2 and replicates to a majority of the new configuration.
```
s1: c1{s1, s2, s3} unreachable
s2: c2{s1, s2, s3, s4} offline
s3: c5{s3, s4, s5} Leader
s4: c5{s3, s4, s5}
s5: c5{s3, s4, s5}
```

Step 5: Administrator brings back s2 with a new disk and the same identity.
```
s1: c1{s1, s2, s3 } unreachable
s2: {}
s3: c5{s3, s4, s5 } Leader
s4: c5{s3, s4, s5 }
s5: c5{s3, s4, s5 }
```

Step 6: s1 becomes reachable again and it starts an election. s2 votes for s1 and s2 still being on the first configuration has a majority and becomes leader. s1 replicates
to s2 and s2 truncates it log, assuming configuration c1.
```
s1: c1{s1, s2, s3} Leader
s2: c1{s1, s2, s3}
s3: c5{s3, s4, s5} Leader
s4: c5{s3, s4, s5}
s5: c5{s3, s4, s5}
```