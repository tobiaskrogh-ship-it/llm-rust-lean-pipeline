/// n cars going each direction; every left-to-right car eventually crosses
/// every right-to-left car ⇒ n × n total "collisions".
pub fn car_race_collision(x: u64) -> u64 {
    x * x
}
