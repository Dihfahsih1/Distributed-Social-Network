sig User {}
sig Post {}

// signature defines a set of objects
sig SocialNetwork {
    posts : User -> Post,   // The set of posts owned by each user
    friends : User -> User // Friendships between users
}

// A fact imposes a constraint that must be satisfied by every instance.
fact friendshipIsSymmetric {
    all n : SocialNetwork, u1, u2 : User |
    u1 -> u2 in n.friends implies
    u2 -> u1 in n.friends
}


// A predicate is a construct for packaging and reusing constraints.
pred invariant[n : SocialNetwork] {
    // Each post is owned by at most one user
    all p : Post | lone n.posts.p
    // A user cannot be his or her own friend
    all u : User | u -> u not in n.friends
    // Friendship is a symmetric relation
    n.friends = ~(n.friends)
}

run generateValidSocialNetwork {
    some n : SocialNetwork | invariant[n]
}

sig DistributedSocialNetwork {
    // Servers where posts are stored
    servers : set Server , 
    // Friendships between users
    friends : User -> User
}
sig Server {
    // Each server stores some subset of posts by different users
    posts : User -> Post ,
    // The maximum number of posts that can be stored on this server
    capacity : Int
}

// initial states of DSN
some sig InitDSN in DistributedSocialNetwork {
}{
    #friends=0
    all s : servers | #s.posts = 0 and s.capacity > 0
}

// describes how local and global states are related
pred promote[n, n' : DistributedSocialNetwork, s, s' : Server] {
    // Pre-Condition
    s in n.servers
    // Post-Condition
    n'.servers = (n.servers - s ) + s'
}
