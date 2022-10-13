


sig User {
    posts : set Post
}
sig Post {}

sig DistributedSN{
    posts : User -> Post,   // The set of posts owned by each user
    friends : User -> User // Friendships between users
}
 

fact friendshipIsSymmetric {
    all n : DistributedSN, u1, u2 : User |
    u1 -> u2 in n.friends implies
    u2 -> u1 in n.friends
}

// no shared posts
fact "you can't share posts"{
    all p: Post |
        one u: User |
            p in u.posts
}

// A predicate is a construct for packaging and reusing constraints.
pred invariant[n : DistributedSN] {
    // Each post is owned by at most one user
    all p : Post | lone n.posts.p
    // A user cannot be his or her own friend
    all u : User | u -> u not in n.friends
    // Friendship is a symmetric relation
    n.friends = ~(n.friends)
}

run DistributedSN {
    some n : DistributedSN | invariant[n]
}
//run {} for 2 but exactly 1 DistributedSN