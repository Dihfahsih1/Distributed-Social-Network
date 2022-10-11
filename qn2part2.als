module qn2part2

open qn2part1

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
