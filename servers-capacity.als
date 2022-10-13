module qn2part2

//open qn2part1
sig User {}
sig Post {}
sig DistributedSocialNetwork {
    // Servers where posts are stored
    servers : set Server , 
    // Friendships between users
    friend_s : User -> User
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
    #friend_s=0
    all s : servers | #s.posts = 0 and s.capacity > 0
}


run {} for 4 but exactly 1 DistributedSocialNetwork 