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

// add new server to the distributed network n1[DOUBTED]

// what it means for a social network to be in a valid state
pred invariant [n1 : DistributedSN ] {
    // 1. friendship is symmetric
    n1.friends = ~(n1.friends)
    // 2. a user cannot be his or her own friend
    no u : User| u->u in n1.friends
    // 3. a post cannot be owned by more than one user
    all p : Post | lone n1.posts.p
}

//add new server s to network n1.
pred addServer[n1, n2:DistributedSN,s1, s2 :Server] {
    //pre-Condition
    s1 in n1

}

pred promote[n, n' : DistributedSocialNetwork, s, s' : Server] {
    // Pre-Condition
    s in n.servers
    // Post-Condition
    n'.servers = (n.servers - s ) + s'
}





// assertion checks addPost preserves the the invariant
assert AddPostPreservesInv {
    // base case
    all sni : InitSN | invariant[sni]
    // inductive case
    all n1, n2 : DistributedSN, u : User, p : Post |
        invariant[n1] and addPost[n1, n2, u, p] implies
            invariant[n2]
}
check AddPostPreservesInv for 5

// assertion checks delPost preserves the the invariant
assert delPostPreservesInv {
    // base case
    all sni : InitSN | invariant[sni]
    // inductive case
    all n1, n2 : DistributedSN, u : User, p : Post |
        invariant[n1] and delPost[n1, n2, u, p] implies
            invariant[n2]
}

check delPostPreservesInv for 5



run invariant for 4 but exactly 1 DistributedSN