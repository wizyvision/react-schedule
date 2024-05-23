import React from 'react';
import Box from '@mui/material/Box';
import Grid from '@mui/material/Grid';
import Typography from '@mui/material/Typography'
import { darken } from '@mui/system';

import { StyledAvatar } from '../../container/Avatar';

function ResourceName(props) {
  const { name, color} = props;
  return (
    <Grid container fullWidth>
      <Grid item xs={3}>
        <StyledAvatar
          sx={{
            backgroundColor: color,
            borderColor: darken(color, 0.35),
          }}
        >
          <Typography
            variant='body1'
            sx={{
              color: darken(color, 0.5),
              fontSize: '16px',
              fontWeight: '600',
            }}
          >
            {Array.from(name)[0]}
          </Typography>
        </StyledAvatar>
      </Grid>
      <Grid item xs={9} sx={{ display: 'flex', alignItems: 'center'}}>
        {name}
      </Grid>
    </Grid>
  );
}

export default ResourceName;
