

 sig User {
    posts : set Post
}
sig Post {}

sig DistributedSN {
    posts : User -> Post,   // The set of posts owned by each user
    friends : User -> User, // Friendships between users
    servers : set Server , 
}

sig Server {
    // Each server stores some subset of posts by different users
    posts : User -> Post ,
    // The maximum number of posts that can be stored on this server
    capacity : Int
}
 
some sig InitSN in DistributedSN {
}{
    //#posts=0
    #friends=0
    #servers=0
    all s : servers | #s.posts = 0 and s.capacity > 0
}
pred postOp[n1, n2 : DistributedSN] {
    n2.friends = n1.friends
    n2.servers = n1.servers
}

// A predicate is a construct for packaging and reusing constraints.
//// what it means for a social network to be in a valid state
pred invariant[n : DistributedSN] {
    // Each post is owned by at most one user
    all p : Post | lone n.posts.p

    // A user cannot be his or her own friend
    no u : User | u -> u in n.friends

    // Friendship is a symmetric relation
    n.friends = ~(n.friends)

    // The number of posts in each server can't exceed its capacity
    all s : n.servers | #s.posts <= s.capacity

    //each post is stored in at most one server
     all s1,s2 : n.servers | s1 != s2 implies no (s1.posts[User] & s2.posts[User])

}

// add a new post ‘‘p’’ to those belonging to user ‘‘u’’
pred addPost [n1, n2 : DistributedSN , u : User , p : Post ] {
    // Pre-condition
    p not in n1.posts[User]
    // Post-condition
    n2.posts = n1.posts + u->p
    // Frame Condition
    postOp[n1,n2]
}

// delete an existing post ‘‘p’’ from user ‘‘u’’
pred delPost [n1, n2 : DistributedSN , u : User , p : Post ] {
    // Pre-condition
    u->p in n1.posts
    // Post-condition
    n2.posts = n1.posts - u->p
    // Frame Condition
    postOp[n1,n2]
}

// add a friend  ‘‘v’’ to user ‘‘u’’
pred addFriend [n1, n2 : DistributedSN , u, v : User] {
    // Pre-condition
    v not in n1.friends[User]
    // Post-condition
    n2.friends = n1.friends + u->v
    // Frame Condition
    postOp[n1,n2]
}


//add new server s to network n1.
pred addServer[n1, n2:DistributedSN, s :Server] {
    //pre-Condition
    s not in n1.servers
    n2.servers=(n1.servers) + s
     // Frame Condition
    postOp[n1,n2]

}

//delete server s to network n1.
pred delServer [n1, n2 : DistributedSN , s :Server] {
    // Pre-condition
    s in n1.servers
    // Post-condition
    n2.servers = n1.servers - s
    // Frame Condition
    postOp[n1,n2]
}

//CHECKING WHETHER THE ABOVE INVARIANTS ARE PRESERVED
// assertion checks addPost preserves the the invariant
assert AddPostPreservesInv {
    // base case
    all sni : InitSN | invariant[sni]
    // inductive case
    all n1, n2 : DistributedSN, u : User, p : Post |
        invariant[n1] and addPost[n1, n2, u, p] implies
            invariant[n2]
}
check AddPostPreservesInv for 4 but exactly 1 DistributedSN

//assertion checks delPost preserves the the invariant
assert delPostPreservesInv {
    // base case
    all sni : InitSN | invariant[sni]
    // inductive case
    all n1, n2 : DistributedSN, u : User, p : Post |
        invariant[n1] and delPost[n1, n2, u, p] implies
            invariant[n2]
}
check delPostPreservesInv for 2 but exactly 1 DistributedSN


//CHECKING ALGEBRAIC PROPERTIES
//checking whether if we add a post and the delete it, do we still have the original state?
check delPostUndoesaddPost {
    all n1, n2, n3 : DistributedSN, u : User, p : Post |
        invariant[n1] and
        addPost[n1,n2,u,p] and delPost[n2,n3,u,p] implies
            n1.posts = n3.posts
}

run {} for 5 but exactly 1 DistributedSN