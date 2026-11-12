use super::LayoutError;

pub struct Blocks<'a> {
    pub paths: &'a [Vec<usize>],
    pub boundary: &'a [i8],
    pub declaration: &'a [i32],
    pub neighbours: &'a [Vec<usize>],
    pub positions: &'a [i64],
}

impl Blocks<'_> {
    pub fn initial(&self, layer: &mut [usize], depth: usize) -> Result<(), LayoutError> {
        if depth > 64 {
            return Err(LayoutError::Domain);
        }
        let mut blocks: Vec<(Option<usize>, Vec<usize>)> = Vec::new();
        for &v in layer.iter() {
            let group = self.paths[v].get(depth).copied();
            if let Some(index) =
                group.and_then(|group| blocks.iter().position(|(key, _)| *key == Some(group)))
            {
                blocks[index].1.push(v);
            } else {
                blocks.push((group, vec![v]));
            }
        }
        let mut output = Vec::with_capacity(layer.len());
        for side in [1, 0, 2] {
            for (group, members) in &mut blocks {
                let boundary = if group.is_none() {
                    self.boundary[members[0]]
                } else {
                    0
                };
                if boundary != side {
                    continue;
                }
                if group.is_some() {
                    self.initial(members, depth + 1)?;
                }
                output.extend_from_slice(members);
            }
        }
        layer.copy_from_slice(&output);
        Ok(())
    }
    pub fn order(&self, layer: &mut [usize], depth: usize) -> Result<(), LayoutError> {
        if depth > 64 {
            return Err(LayoutError::Domain);
        }
        let mut blocks: Vec<(Option<usize>, Vec<usize>)> = Vec::new();
        for &v in layer.iter() {
            let group = self.paths[v].get(depth).copied();
            if let Some(index) =
                group.and_then(|group| blocks.iter().position(|(key, _)| *key == Some(group)))
            {
                blocks[index].1.push(v);
            } else {
                blocks.push((group, vec![v]));
            }
        }
        let mut keyed = Vec::new();
        for (group, mut members) in blocks {
            if group.is_some() {
                self.order(&mut members, depth + 1)?;
            }
            let (mut sum, mut count) = (0i64, 0i64);
            for &v in &members {
                for &w in &self.neighbours[v] {
                    sum = sum
                        .checked_add(self.positions[w])
                        .ok_or(LayoutError::Overflow)?;
                    count += 1;
                }
            }
            if count == 0 {
                for &v in &members {
                    sum = sum
                        .checked_add(self.positions[v])
                        .ok_or(LayoutError::Overflow)?;
                    count += 1;
                }
            }
            let boundary = if group.is_none() {
                self.boundary[members[0]]
            } else {
                0
            };
            let priority = match boundary {
                1 => -1,
                2 => 1,
                _ => 0,
            };
            let declaration = members
                .iter()
                .map(|&v| self.declaration[v])
                .min()
                .ok_or(LayoutError::Domain)?;
            keyed.push((priority, sum, count, declaration, group, members));
        }
        keyed.sort_by(|a, b| {
            a.0.cmp(&b.0)
                .then_with(|| {
                    (i128::from(a.1) * i128::from(b.2)).cmp(&(i128::from(b.1) * i128::from(a.2)))
                })
                .then_with(|| a.3.cmp(&b.3))
                .then_with(|| a.4.cmp(&b.4))
        });
        let mut index = 0;
        for (_, _, _, _, _, members) in keyed {
            for v in members {
                layer[index] = v;
                index += 1;
            }
        }
        Ok(())
    }
}
