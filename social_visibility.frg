#lang forge/froglet

/* Social Media Visibility Model
 * A formal model verifying the access control logic of a social media feature. 
 * It handles complex privacy interactions between global account settings, social relationships (friends/block/mute), 
 * and granular post-level visibility (public/private/whitelist/blacklist).
 */

option run_sterling "vis.js"

abstract sig Boolean {}
one sig True, False extends Boolean {}

// social visibility： including public, friends-only, specific friends, exclude friends, private
abstract sig Visibility {}
one sig Public, FriendsOnly, SpecificFriends, ExcludeFriends, Private extends Visibility {}

sig User {
    friends: pfunc User -> Boolean,
    blocked: pfunc User -> Boolean,    // list of users I have blocked
    muted: pfunc User -> Boolean,      // list of users whose moments I have muted
    
    // account settings
    stranger_see_recent: one Boolean,  // allows strangers to see recent posts
    moments_closed: one Boolean,       // global switch to turn off moments
    limit_recent_10: one Boolean       // only allow recent 10 posts to be visible
}

sig Post {
    author: one User,
    visibility: one Visibility,
    allowed_viewers: pfunc User -> Boolean,  // SpecificFriends
    excluded_viewers: pfunc User -> Boolean, // ExcludeFriends
    timestamp: one Int
}



pred wellformed {
    all u: User | u.friends[u] != True // can't be friend with oneself
    all u1, u2: User | u2.friends[u1] = True implies u1.friends[u2] = True // friendship is mutual
    
    // blocklist
    all u: User | u.blocked[u] != True // can't block oneself
    all u1, u2: User | u1.blocked[u2] = True implies u1.friends[u2] != True // can't be friend with someone you blocked
    
    // mutelist
    all u: User | u.muted[u] != True // can't mute oneself
    
    all p: Post | p.timestamp >= 0 
    all disj p1, p2: Post | (p1.author = p2.author) implies p1.timestamp != p2.timestamp // can't have two posts with the same timestamp from the same author
    
    all p: Post, u: User | (p.visibility = SpecificFriends and p.allowed_viewers[u] = True) implies p.author.friends[u] = True
    all p: Post, u: User | p.visibility != SpecificFriends implies p.allowed_viewers[u] != True
    
    // you can only exclude friends, and if you exclude someone, they must be your friend
    all p: Post, u: User | (p.visibility = ExcludeFriends and p.excluded_viewers[u] = True) implies p.author.friends[u] = True
    all p: Post, u: User | p.visibility != ExcludeFriends implies p.excluded_viewers[u] != True
}

// isRecent：only the most recent 10 posts from the same author are considered recent. 
pred isRecent[p: Post] {
    #{other_p: Post | other_p.author = p.author and other_p.timestamp > p.timestamp} < 10
}

pred canSee[viewer: User, p: Post] {
    // you can always see your own posts
    viewer = p.author 
    or 
    (
        viewer != p.author 
        
        // if it's not your own post, you must not be blocked by the author
        and p.author.blocked[viewer] != True
        
        // if I have muted the author, I can't see their posts
        and viewer.muted[p.author] != True
        
        // if moments is closed, no one can see the posts
        and p.author.moments_closed = False 
        and (p.author.limit_recent_10 = False or isRecent[p]) // check the visibility settings
        
        and 
        (
            // friend's view
            (
                p.author.friends[viewer] = True and ( 
                    p.visibility = Public 
                    or p.visibility = FriendsOnly 
                    or (p.visibility = SpecificFriends and p.allowed_viewers[viewer] = True) 
                    or (p.visibility = ExcludeFriends and p.excluded_viewers[viewer] != True)
                )
            )
            or 
            // stranger's view
            (
                p.author.friends[viewer] != True and ( 
                    p.visibility = Public 
                    and p.author.stranger_see_recent = True 
                    and isRecent[p] 
                )
            )
        )
    )
}

-- test cases for the known scenario 
// Scenario Summary: Tests visibility of 4 different posts by Alice against 3 distinct viewers:
// 1. Bob (Friend, but muted Alice): Sees NOTHING due to receiver-side block.
// 2. Dave (Friend): Sees 'Public' and 'SpecificFriends' (he is allowed), but NOT 'ExcludeFriends' (he is explicitly excluded).
// 3. Charlie (Stranger): Sees ONLY the recent 'Public' post (due to Alice's 'stranger_see_recent' setting).

pred known_scenario {
    
    some disj Alice, Bob, Charlie, Dave: User |
    some disj p_pub, p_priv, p_spec, p_excl: Post | {
        
        Bob.friends[Alice] = True
        Alice.friends[Bob] = True
        Dave.friends[Alice] = True
        Alice.friends[Dave] = True
        all u: User | Charlie.friends[u] != True
        
        Bob.muted[Alice] = True
        
        Alice.stranger_see_recent = True
        Alice.moments_closed = False     
        Alice.limit_recent_10 = True     

        p_pub.author = Alice and p_pub.visibility = Public and p_pub.timestamp = 10
        p_priv.author = Alice and p_priv.visibility = Private and p_priv.timestamp = 9
        p_spec.author = Alice and p_spec.visibility = SpecificFriends and p_spec.allowed_viewers[Dave] = True and p_spec.timestamp = 8
        p_excl.author = Alice and p_excl.visibility = ExcludeFriends and p_excl.excluded_viewers[Dave] = True and p_excl.timestamp = 7

        not canSee[Bob, p_pub]          
        not canSee[Bob, p_priv]    
        not canSee[Bob, p_spec]         
        not canSee[Bob, p_excl]

        canSee[Dave, p_pub]
        canSee[Dave, p_spec]
        not canSee[Dave, p_excl]
        
        canSee[Charlie, p_pub]      
    }
}

run {
    wellformed
    known_scenario
} for 5 Int, exactly 4 User, exactly 4 Post
