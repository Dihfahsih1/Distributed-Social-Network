module qn2part1

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
